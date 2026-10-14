/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence

/-!
# The index filtration of a twisted complex

Let `m` be a twisting cocycle on the finite set `P` of generators graded by `ind`, and let
`(ℳ, dM)` be a differential graded right module.  The **index filtration** of the twisted complex
`ℳ ⊗ ⟨P⟩` is the increasing filtration whose `p`-th piece

`F_p = ⊕_{ind x ≤ p} ℳ ⊗ ⟨x⟩`

consists of the families `P → M` supported on the generators of index at most `p`.  The twisted
differential `D (α ⊗ x) = dM α ⊗ x + (-1) ^ |α| Σ_y (α · m x y) ⊗ y` preserves it, because
`m x y = 0` unless `ind y < ind x`: this is where the one-sidedness of a twisting cocycle is used.
Since `P` is finite the filtration is finite, `F_p = 0` below every index and `F_p` is everything
above every index, so its spectral sequence converges strongly to the cohomology of the twisted
complex.  It is the algebraic counterpart of the filtration of a Morse or Floer complex with DG
coefficients by the Morse index, whose spectral sequence compares DG Morse homology with the
Serre spectral sequence of a fibration.

The filtration is first set up on modules for an arbitrary matrix satisfying the one-sidedness
condition (`TauCeti.twistedDifferential_mem_indexFiltrationSubmodule`), then packaged as a
filtration of the twisted cochain complex by subcomplexes, through
`TauCeti.gradedCochainComplexSubobject`, and fed to the spectral sequence of a filtered complex
of `TauCeti.Algebra.Homology.SpectralSequence.Filtered`.

## Main definitions

* `TauCeti.indexFiltrationSubmodule ind p`: the families `P → M` vanishing on the generators of
  index greater than `p`.
* `TauCeti.TwistingCocycle.indexFiltration`: the index filtration of the twisted complex, by
  subcomplexes.
* `TauCeti.TwistingCocycle.indexSpectralSequence`: its spectral sequence.

## Main results

* `TauCeti.twistedDifferential_mem_indexFiltrationSubmodule`: the twisted differential of a
  one-sided matrix preserves the index filtration.
* `TauCeti.TwistingCocycle.monotone_indexFiltration`, `indexFiltration_eq_bot`,
  `indexFiltration_eq_top`: the index filtration is increasing and finite.
* `TauCeti.TwistingCocycle.indexSpectralSequencePageXIsoGraded`: strong convergence of the index
  spectral sequence to the cohomology of the twisted complex.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

section Submodule

variable {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M]
  {P : Type uP} (ind : P → ℤ)

/-- The `p`-th piece of the index filtration on `P → M`: the families supported on the generators
of index at most `p`, that is, vanishing on every generator of index greater than `p`. -/
def indexFiltrationSubmodule (p : ℤ) : Submodule R (P → M) :=
  Submodule.pi {x | p < ind x} fun _ ↦ ⊥

variable {ind}

@[simp]
theorem mem_indexFiltrationSubmodule_iff {p : ℤ} {f : P → M} :
    f ∈ indexFiltrationSubmodule (R := R) ind p ↔ ∀ x, p < ind x → f x = 0 := by
  simp [indexFiltrationSubmodule, Submodule.mem_pi]

variable (R M ind) in
/-- The index filtration is increasing. -/
theorem monotone_indexFiltrationSubmodule :
    Monotone (indexFiltrationSubmodule (R := R) (M := M) ind) := by
  intro p q hpq f hf
  rw [mem_indexFiltrationSubmodule_iff] at hf ⊢
  exact fun x hx ↦ hf x (hpq.trans_lt hx)

/-- Above every index, the index filtration is everything. -/
theorem indexFiltrationSubmodule_eq_top {p : ℤ} (h : ∀ x, ind x ≤ p) :
    indexFiltrationSubmodule (R := R) (M := M) ind p = ⊤ := by
  refine eq_top_iff.2 fun f _ ↦ mem_indexFiltrationSubmodule_iff.2 fun x hx ↦ ?_
  exact absurd (h x) (not_le.2 hx)

/-- Below every index, the index filtration vanishes. -/
theorem indexFiltrationSubmodule_eq_bot {p : ℤ} (h : ∀ x, p < ind x) :
    indexFiltrationSubmodule (R := R) (M := M) ind p = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  rw [mem_indexFiltrationSubmodule_iff] at hf
  exact (Submodule.mem_bot R).2 (funext fun x ↦ hf x (h x))

end Submodule

section Differential

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Semiring A]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  (m : P → P → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

/-- The twisted differential of a matrix satisfying the one-sidedness condition preserves the
index filtration: a generator `x` only contributes to the components `y` with `ind y < ind x`. -/
theorem twistedDifferential_mem_indexFiltrationSubmodule
    (hm : ∀ x y, ind x ≤ ind y → m x y = 0) {p : ℤ} {f : P → M}
    (hf : f ∈ indexFiltrationSubmodule (R := R) ind p) :
    twistedDifferential m ℳ dM f ∈ indexFiltrationSubmodule (R := R) ind p := by
  rw [mem_indexFiltrationSubmodule_iff] at hf ⊢
  intro y hy
  rw [twistedDifferential_apply, hf y hy, map_zero, zero_add]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  rcases le_or_gt (ind x) p with hx | hx
  · rw [hm x y (hx.trans hy.le), MulOpposite.op_zero, zero_smul]
  · rw [hf x hx, map_zero, smul_zero]

end Differential

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM)

/-- The **index filtration** of the twisted complex `ℳ ⊗ ⟨P⟩` of a twisting cocycle: its `p`-th
piece is the subcomplex `⊕_{ind x ≤ p} ℳ ⊗ ⟨x⟩` of the families supported on the generators of
index at most `p`.  The subcomplex is cut out of `gradedCochainComplex` by
`indexFiltrationSubmodule ind p` and transported along
`twistedCochainComplex_eq_gradedCochainComplex`. -/
noncomputable def indexFiltration (p : ℤ) : Subobject (m.twistedCochainComplex dM hM) :=
  Subobject.mapIsoToOrderIso
    (eqToIso (twistedCochainComplex_eq_gradedCochainComplex m.mem_graded m.twisting hM).symm)
    (gradedCochainComplexSubobject _ _ _ _ (indexFiltrationSubmodule ind p) fun _ hf ↦
      twistedDifferential_mem_indexFiltrationSubmodule m.m dM m.one_sided hf)

/-- The `p`-th piece of the index filtration is the subcomplex of `gradedCochainComplex` cut out
by `indexFiltrationSubmodule ind p`, transported along
`twistedCochainComplex_eq_gradedCochainComplex`. -/
theorem indexFiltration_eq (p : ℤ) :
    m.indexFiltration dM hM p = Subobject.mapIsoToOrderIso
      (eqToIso (twistedCochainComplex_eq_gradedCochainComplex m.mem_graded m.twisting hM).symm)
      (gradedCochainComplexSubobject _ _ _ _ (indexFiltrationSubmodule ind p) fun _ hf ↦
        twistedDifferential_mem_indexFiltrationSubmodule m.m dM m.one_sided hf) := by
  rw [indexFiltration]

/-- The index filtration is increasing. -/
theorem monotone_indexFiltration : Monotone (m.indexFiltration dM hM) := fun _ _ hpq ↦
  (Subobject.mapIsoToOrderIso _).monotone
    (gradedCochainComplexSubobject_mono _ _ (monotone_indexFiltrationSubmodule R M ind hpq))

/-- Above every index, the index filtration is the whole twisted complex. -/
theorem indexFiltration_eq_top {p : ℤ} (hp : ∀ x, ind x ≤ p) : m.indexFiltration dM hM p = ⊤ := by
  rw [indexFiltration_eq,
    gradedCochainComplexSubobject_eq_top _ (indexFiltrationSubmodule_eq_top hp), OrderIso.map_top]

/-- Below every index, the index filtration is the zero subcomplex. -/
theorem indexFiltration_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) : m.indexFiltration dM hM p = ⊥ := by
  rw [indexFiltration_eq,
    gradedCochainComplexSubobject_eq_bot _ (indexFiltrationSubmodule_eq_bot hp), OrderIso.map_bot]

/-- The **index spectral sequence** of the twisted complex of a twisting cocycle: the spectral
sequence of its index filtration.  On its first page, numbered `2`, the object at `(p, q)` is the
cohomology `H^{p+q}(F_{q+1} / F_q)` of a graded piece of the index filtration
(`CochainComplex.spectralSequenceFirstPageXIsoCokernel`). -/
noncomputable abbrev indexSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor (m.indexFiltration dM hM) (m.monotone_indexFiltration dM hM))

/-- **Strong convergence of the index spectral sequence.** If every index lies in the interval
`(a, b]`, then on every page `r ≥ 2` with `q - r + 2 ≤ a` and `b ≤ q + r - 1`, the object at
`pq = (p, q)` is the graded piece `F_{q+1} H^{p+q} / F_q H^{p+q}` of the filtration of the
cohomology `H^{p+q}` of the twisted complex (identified with the abutment by
`CochainComplex.filtrationAbutmentIso`). -/
noncomputable def indexSpectralSequencePageXIsoGraded {a b : ℤ} (ha : ∀ x, a < ind x)
    (hb : ∀ x, ind x ≤ b) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((m.indexSpectralSequence dM hM).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (m.indexFiltration dM hM) (m.monotone_indexFiltration dM hM))).abutmentFiltrationMap pq.2
          (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (m.indexFiltration_eq_bot dM hM ha) (m.indexFiltration_eq_top dM hM hb) r hr pq hra hrb

end TwistingCocycle

end TauCeti
