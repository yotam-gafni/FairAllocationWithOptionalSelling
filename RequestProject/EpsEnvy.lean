import Mathlib
import RequestProject.Selling

/-!
# ε-relaxations of the envy notions (Appendix C, Definition 8)

The manuscript's Definition 8 introduces, for a tolerance `ε ≥ 0`, the notions `ε-SEF1` and
`ε-SEFX`:

> An allocation `(A₁,P₁), …, (Aₙ,Pₙ)` is envy free (EF) if for every agent `i` and other agent
> `j`, `v̄ᵢ(Aᵢ) + Pᵢ ≥ v̄ᵢ(A_j) + P_j`.  An allocation satisfies the following relaxations of EF
> if the above envy free condition holds whenever `P_j > 0`, and the following relaxed conditions
> hold if `P_j = 0`.
> 1. `ε-SEF1`: `v̄ᵢ(Aᵢ) + Pᵢ + ε ≥ v̄ᵢ(A_j \ g) + p(g)` for *some* good `g ∈ A_j`.
> 2. `ε-SEFX`: `v̄ᵢ(Aᵢ) + Pᵢ + ε ≥ v̄ᵢ(A_j \ g) + p(g)` for *every* good `g ∈ A_j`.

As in Definition 4 (see `SEF1` in `RequestProject.Selling`), the relaxed conditions carry the
envying agent's own money `Pᵢ` on the left-hand side, and it is also enough that the (`ε`-relaxed)
envy-free condition `v̄ᵢ(Aᵢ) + Pᵢ + ε ≥ v̄ᵢ(A_j)` holds.  The literal transcriptions of the
manuscript's text are recorded as `epsSEF1lit` and `epsSEFXlit`.

For `ε = 0` these are exactly the notions `SEF1` and `SEFX` of Definition 4, which are already
formalized in `RequestProject.Selling`; this is checked below (`epsSEF1_zero_iff`,
`epsSEFX_zero_iff`, and `epsSEF1lit_zero_iff`, `epsSEFXlit_zero_iff` for the literal forms).

## Two further variants

Besides the notions above, this file records two variants of `SEFX` that differ from Definition
4/8 only in *where the money is accounted for*:

* `SEFXu` ("utility form"): the envied agent's bundle, with one good removed, is compared to the
  envying agent's *utility* `v̄ᵢ(Aᵢ) + Pᵢ`, and the envied agent's money `P_j` is charged on the
  right-hand side, whether or not it is positive.  This is the notion of envy-freeness up to any
  good for mixed divisible/indivisible goods (`EFXM`), transported to the present setting.  For
  valid outcomes it is *equivalent* to the corrected `SEFX` (`SEFX_iff_SEFXu`), which is what
  makes Lemma 11 go through in `RequestProject.LemmaEleven`; for the literal `SEFXlit` it is not,
  and indeed Lemma 11 fails for `SEFXlit`.
* `SEFXs` ("strong form"): as `SEFXu` but with the envying agent's own money not counted.  It is
  *stronger* than `SEFX` (`SEFX_of_SEFXs`) and than `SEFXlit` (`SEFXlit_of_SEFXs`).

Both variants are closed conditions, and each admits an `ε`-relaxation.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [DecidableEq G] {n : ℕ}

/-! ### Definition 8 -/

/-- **Definition 8.1**, `ε-SEF1`: for every ordered pair of agents `i, j`, either agent `j` holds
a positive amount of money and the plain envy-free condition holds, or `j` holds no money and
either the `ε`-relaxed envy-free condition `v̄ᵢ(Aᵢ) + Pᵢ + ε ≥ v̄ᵢ(A_j)` holds or there is a good
`g ∈ A_j` with `v̄ᵢ(Aᵢ) + Pᵢ + ε ≥ v̄ᵢ(A_j \ g) + p g`.

As for `SEF1` (Definition 4.1), the envying agent's own money `Pᵢ` is counted on the left-hand
side of the relaxed condition, and the relaxed condition is a disjunction with the (relaxed)
envy-free condition, which is what makes the notion a relaxation of envy-freeness also for an
empty envied bundle.  The literal transcription of the manuscript's text is `epsSEF1lit`. -/
def epsSEF1 (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i + eps ≥ vbarSum (v i) p (o.kept j)) ∨
      (∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))

/-- **Definition 8.2**, `ε-SEFX`: as `ε-SEF1`, but the up-to-any-good condition must hold for
*every* good of the envied bundle. -/
def epsSEFX (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i + eps ≥ vbarSum (v i) p (o.kept j)) ∨
      (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))

/-- The *literal* transcription of Definition 8.1 (cf. `SEF1lit`): the envying agent's own money
does not appear on the left-hand side, and there is no exemption for an empty envied bundle. -/
def epsSEF1lit (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)

/-- The *literal* transcription of Definition 8.2 (cf. `SEFXlit`). -/
def epsSEFXlit (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)

variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

/-- At `ε = 0`, Definition 8.1 is Definition 4.1. -/
theorem epsSEF1_zero_iff : epsSEF1 v p 0 o ↔ SEF1 v p o := by
  unfold epsSEF1 SEF1
  simp

/-- At `ε = 0`, Definition 8.2 is Definition 4.2. -/
theorem epsSEFX_zero_iff : epsSEFX v p 0 o ↔ SEFX v p o := by
  unfold epsSEFX SEFX
  simp

/-- At `ε = 0`, the literal Definition 8.1 is the literal Definition 4.1. -/
theorem epsSEF1lit_zero_iff : epsSEF1lit v p 0 o ↔ SEF1lit v p o := by
  unfold epsSEF1lit SEF1lit
  simp

/-- At `ε = 0`, the literal Definition 8.2 is the literal Definition 4.2. -/
theorem epsSEFXlit_zero_iff : epsSEFXlit v p 0 o ↔ SEFXlit v p o := by
  unfold epsSEFXlit SEFXlit
  simp

/-- `ε-SEFX` is monotone in `ε`. -/
theorem epsSEFX_mono {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEFX v p eps o) :
    epsSEFX v p eps' o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => ?_⟩
  rcases (ho i j).2 hj with hEF | hall
  · exact Or.inl (by linarith)
  · exact Or.inr fun g hg => le_trans (hall g hg) (by linarith)

/-- `ε-SEF1` is monotone in `ε`. -/
theorem epsSEF1_mono {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEF1 v p eps o) :
    epsSEF1 v p eps' o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => ?_⟩
  rcases (ho i j).2 hj with hEF | ⟨g, hg, hle⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨g, hg, le_trans hle (by linarith)⟩

/-- The literal `ε-SEFX` implies the corrected `ε-SEFX`, for a valid outcome. -/
theorem epsSEFX_of_epsSEFXlit {eps : ℝ} (hvalid : o.Valid p) (ho : epsSEFXlit v p eps o) :
    epsSEFX v p eps o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (ho i j).2 hj g hg
  have hmi := hvalid.2.2.1 i
  linarith

/-- `SEFX` implies `ε-SEFX` for every `ε ≥ 0`. -/
theorem epsSEFX_of_SEFX {eps : ℝ} (heps : 0 ≤ eps) (ho : SEFX v p o) : epsSEFX v p eps o :=
  epsSEFX_mono heps (epsSEFX_zero_iff.2 ho)

/-! ### The utility form of `SEFX` -/

/-- `ε-SEFXu`: the *utility form* of `ε-SEFX`.  The envying agent compares its whole utility
`v̄ᵢ(Aᵢ) + Pᵢ` (goods **and** money) with `v̄ᵢ(A_j \ g) + p(g) + P_j`.  Stated unconditionally in
`P_j`, together with the plain envy-free condition when `P_j > 0`. -/
def epsSEFXu (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i + eps
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)

/-- `SEFXu`, the utility form of `SEFX` (that is, `ε-SEFXu` with `ε = 0`). -/
def SEFXu (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)

theorem epsSEFXu_zero_iff : epsSEFXu v p 0 o ↔ SEFXu v p o := by
  unfold epsSEFXu SEFXu
  simp

/-- Splitting off one good from a bundle, measured with `v̄ᵢ`. -/
theorem vbarSum_erase {vi p : G → ℝ} {A : Finset G} {g : G} (hg : g ∈ A) :
    vbarSum vi p A = vbarSum vi p (A \ {g}) + vbar vi p g :=
  vbarSum_sdiff_singleton hg

omit [DecidableEq G] in
theorem p_le_vbar {vi p : G → ℝ} (g : G) : p g ≤ vbar vi p g := le_max_left _ _

/-- `SEFX` (Definition 4.2, corrected) implies its utility form, for a valid outcome. -/
theorem SEFXu_of_SEFX (hvalid : o.Valid p) (ho : SEFX v p o) : SEFXu v p o := by
  intro i j
  refine ⟨(ho i j).1, fun g hg => ?_⟩
  have hsplit := vbarSum_erase (vi := v i) (p := p) hg
  have hpg : p g ≤ vbar (v i) p g := p_le_vbar g
  rcases lt_or_eq_of_le (hvalid.2.2.1 j) with hj | hj
  · -- `j` holds money: use the envy-free condition and drop the good `g`.
    have hEF := (ho i j).1 hj
    linarith
  · have hj0 : o.money j = 0 := hj.symm
    rw [hj0]
    rcases (ho i j).2 hj0 with hEF | hall
    · linarith
    · have := hall g hg
      linarith

/-- Conversely, the utility form implies `SEFX` (Definition 4.2, corrected): the two notions
are in fact equivalent, which is what makes Lemma 11 go through for the corrected notion. -/
theorem SEFX_of_SEFXu (ho : SEFXu v p o) : SEFX v p o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (ho i j).2 g hg
  rw [hj] at this
  linarith

/-- `SEFX` (corrected) and its utility form coincide, for a valid outcome. -/
theorem SEFX_iff_SEFXu (hvalid : o.Valid p) : SEFX v p o ↔ SEFXu v p o :=
  ⟨SEFXu_of_SEFX hvalid, SEFX_of_SEFXu⟩

/-! ### The strong form of `SEFX` -/

/-- `ε-SEFXs`: the *strong form* of `ε-SEFX`.  The money `P_j` of the envied agent is charged
also when it is positive, and the envying agent's own money is not counted. -/
def epsSEFXs (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i + eps
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)

/-- `SEFXs`, the strong form of `SEFX` (that is, `ε-SEFXs` with `ε = 0`). -/
def SEFXs (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i)
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)

theorem epsSEFXs_zero_iff : epsSEFXs v p 0 o ↔ SEFXs v p o := by
  unfold epsSEFXs SEFXs
  simp

/-- The strong form implies `SEFX` (Definition 4.2), for a valid outcome. -/
theorem SEFX_of_SEFXs (hvalid : o.Valid p) (ho : SEFXs v p o) : SEFX v p o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (ho i j).2 g hg
  have hmi := hvalid.2.2.1 i
  rw [hj] at this
  linarith

/-- The strong form implies the literal `SEFX` (Definition 4.2 as written). -/
theorem SEFXlit_of_SEFXs (ho : SEFXs v p o) : SEFXlit v p o := by
  intro i j
  refine ⟨(ho i j).1, fun hj g hg => ?_⟩
  have := (ho i j).2 g hg
  rw [hj] at this
  linarith

/-- The strong form implies the utility form, for a valid outcome. -/
theorem SEFXu_of_SEFXs (hvalid : o.Valid p) (ho : SEFXs v p o) : SEFXu v p o :=
  SEFXu_of_SEFX hvalid (SEFX_of_SEFXs hvalid ho)

/-- `ε-SEFX` (Definition 8.2) implies the utility form `ε-SEFXu`, for a valid outcome:
this is the (only) step where the two notions of Definition 4/8 and their utility forms are
compared, and it is what makes the corrected Lemma 11 applicable to the manuscript's notion. -/
theorem epsSEFXu_of_epsSEFX {eps : ℝ} (heps : 0 ≤ eps) (hvalid : o.Valid p)
    (ho : epsSEFX v p eps o) : epsSEFXu v p eps o := by
  intro i j
  refine ⟨fun hj => by have := (ho i j).1 hj; linarith, fun g hg => ?_⟩
  have hsplit := vbarSum_erase (vi := v i) (p := p) hg
  have hpg : p g ≤ vbar (v i) p g := p_le_vbar g
  rcases lt_or_eq_of_le (hvalid.2.2.1 j) with hj | hj
  · have hEF := (ho i j).1 hj
    linarith
  · have hj0 : o.money j = 0 := hj.symm
    rw [hj0]
    rcases (ho i j).2 hj0 with hEF | hall
    · linarith
    · have := hall g hg
      linarith

end FairSelling
