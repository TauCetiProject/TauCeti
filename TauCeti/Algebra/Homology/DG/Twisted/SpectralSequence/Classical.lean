/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.E2

/-!
# The classical complex on the cohomology of a DG module

The second page of the index spectral sequence of a twisted complex is the homology of the
classical complex `TauCeti.TwistingCocycle.indexClassicalComplex`, whose terms are products of the
cohomology of `shiftedModuleComplex hM q`, a reindexing of the complex of a DG right module `ℳ`,
and whose entries are the actions of the cycles `m x y` of degree zero. The cohomology of
`shiftedModuleComplex hM p` in degree `n` is the piece `H^{n + p}(ℳ)` of the intrinsic cohomology
`H(ℳ)` of the module (`TauCeti.shiftedModuleComplexHomologyEquiv`), and under these
identifications the action of a cycle `a` of degree zero twisted by the Koszul sign
(`TauCeti.shiftedModuleComplexActHomology`) is the action of the class of `a` in `H(A)`, with the
sign `(-1)^j` on `H^j(ℳ)`
(`TauCeti.shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology`).

This file defines the class in `H(A)` of an entry `m x y` of index difference one, which lies in
`H⁰(A)`, and computes, under these identifications, the entries and the components of the
differential of the classical complex in coefficient degree `k`: componentwise, the entry between
generators `x` and `y` is `(-1)^k` times the action on `H^k(ℳ)` of the class of `m x y`
(`TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`).

It then assembles these identifications into an isomorphism of complexes. The complex
`TauCeti.TwistingCocycle.indexCohomologyComplex` has in degree `q` the families indexed by the
generators of index `q` with values in `H^k(ℳ)`, and as differential the matrix of the
endomorphisms `(-1)^k [m x y]` of `H^k(ℳ)`. The classical complex is isomorphic to it
(`TauCeti.TwistingCocycle.indexClassicalComplexIso`), so the second page of the index spectral
sequence is its homology (`TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIsoCohomology`).
For the chains on Moore loops the entries are those of the truncated cocycle in the group ring of
the fundamental group, acting on the local system `H^k(𝓕)`; see
`TauCeti.AlgebraicTopology.DGLocalSystem.SecondPage`.

## Main definitions

* `TauCeti.TwistingCocycle.indexClassicalClass`: the class in `H(A)` of an entry of index
  difference one.
* `TauCeti.TwistingCocycle.indexCohomologyEntry`: the endomorphism `(-1)^k [m x y]` of `H^k(ℳ)`.
* `TauCeti.TwistingCocycle.indexCohomologyComplex`: the complex of families in `H^k(ℳ)` with the
  matrix of these endomorphisms as differential.
* `TauCeti.TwistingCocycle.indexClassicalComplexIso`: the classical complex is isomorphic to it.

## Main results

* `TauCeti.TwistingCocycle.indexClassicalClass_mem_cohomologyGrading_zero`: this class lies in
  `H⁰(A)`.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`: the entries of
  the classical complex are `(-1)^k` times the actions of the classes of the entries of the
  twisting cocycle.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalD_π`: the components of
  the classical differential are `(-1)^k` times the sums of these actions.
* `TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIsoCohomology`: the second page of the
  index spectral sequence is the homology of `indexCohomologyComplex`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38 and Theorem 3.39.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM) (k : ℤ)

variable (h) in
/-- The class in the cohomology `H(A)` of the entry `m x y` between generators whose indices
differ by one, a cycle of degree zero. -/
noncomputable def indexClassicalClass {x y : P} (hxy : ind x = ind y + 1) : h.Cohomology :=
  Ideal.Quotient.mk h.boundaries.asIdeal
    ⟨m.m x y, h.mem_cycles.mpr (m.d_m_eq_zero_of_eq_add_one hxy)⟩

variable (h) in
theorem indexClassicalClass_def {x y : P} (hxy : ind x = ind y + 1) :
    m.indexClassicalClass h hxy = Ideal.Quotient.mk h.boundaries.asIdeal
      ⟨m.m x y, h.mem_cycles.mpr (m.d_m_eq_zero_of_eq_add_one hxy)⟩ :=
  (rfl)

variable (h) in
/-- The class of an entry of index difference one has degree zero: it lies in `H⁰(A)`. -/
theorem indexClassicalClass_mem_cohomologyGrading_zero {x y : P} (hxy : ind x = ind y + 1) :
    m.indexClassicalClass h hxy ∈ h.cohomologyGrading 0 :=
  h.mem_cohomologyGrading.mpr ⟨_, m.m_mem_zero_of_eq_add_one hxy, rfl⟩

/-- **The entries of the classical complex are the actions of the classes of the entries of the
twisting cocycle**: under the identifications `shiftedModuleComplexHomologyEquiv` of its terms
with `H^k(ℳ)`, the entry of the classical complex in coefficient degree `k` between a generator `x`
of index `q + 1` and a generator `y` of index `q` is `(-1)^k` times the action on `H^k(ℳ)` of
the class of `m x y` in `H⁰(A)`. -/
theorem shiftedModuleComplexHomologyEquiv_indexClassicalEntry (q : ℤ)
    (x : {x : P // ind x = q + 1}) (y : {y : P // ind y = q})
    (c : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q)
        ((m.indexClassicalEntry hM k q x y).hom c) : hM.Cohomology) =
      k.negOnePow • (hM.cohomologyAction
        (m.indexClassicalClass h (x := x.val) (y := y.val) (by rw [x.property, y.property]))).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) (k - (q + 1)) c) := by
  rw [indexClassicalEntry_def, shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology,
    congrArg Int.negOnePow (sub_add_cancel k (q + 1)), indexClassicalClass_def]

/-- **The classical differential on cohomology**: under the identifications
`shiftedModuleComplexHomologyEquiv` of the terms of the classical complex in coefficient degree `k`
with products of copies of `H^k(ℳ)`, the component at a generator `y` of index `q` of the
differential of a family `c` indexed by the generators of index `q + 1` is `(-1)^k` times the sum
of the actions of the classes of the entries `m x y` on the components `c x`. -/
theorem shiftedModuleComplexHomologyEquiv_indexClassicalD_π (q : ℤ) (y : {y : P // ind y = q})
    (c : ↑(∏ᶜ fun _ : {x : P // ind x = q + 1} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1)))) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q)
        ((m.indexClassicalD hM k q ≫ Pi.π _ y).hom c) : hM.Cohomology) =
      k.negOnePow • ∑ x : {x : P // ind x = q + 1}, (hM.cohomologyAction
        (m.indexClassicalClass h (x := x.val) (y := y.val) (by rw [x.property, y.property]))).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) (k - (q + 1))
            ((Pi.π (fun _ : {x : P // ind x = q + 1} ↦
              (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) x).hom
                c)) := by
  rw [indexClassicalD_π, ModuleCat.hom_sum, LinearMap.sum_apply, map_sum, Submodule.coe_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply,
    shiftedModuleComplexHomologyEquiv_indexClassicalEntry]

/-! ### The classical complex as a complex of families in `H^k(ℳ)` -/

/-- The entry of index difference one as an endomorphism of `H^k(ℳ)`: `(-1)^k` times the action of
the class of `m x y` in `H⁰(A)`, which preserves the degree `k`. -/
noncomputable def indexCohomologyEntry {x y : P} (hxy : ind x = ind y + 1) :
    hM.cohomologyGrading k →ₗ[R] hM.cohomologyGrading k :=
  k.negOnePow • (hM.cohomologyAction (m.indexClassicalClass h hxy)).unop.restrict fun _ hc ↦ by
    simpa only [add_zero] using hM.cohomologyAction_apply_mem_cohomologyGrading
      (m.indexClassicalClass_mem_cohomologyGrading_zero h hxy) hc

@[simp]
theorem coe_indexCohomologyEntry_apply {x y : P} (hxy : ind x = ind y + 1)
    (c : hM.cohomologyGrading k) :
    (m.indexCohomologyEntry hM k hxy c : hM.Cohomology) =
      k.negOnePow • (hM.cohomologyAction (m.indexClassicalClass h hxy)).unop c :=
  (rfl)

/-- The differential of the classical complex on families in `H^k(ℳ)`: a family `c` indexed by
the generators of index `q + 1` goes to the family whose component at a generator `y` of index
`q` is `∑ₓ indexCohomologyEntry (c x)`. -/
noncomputable def indexCohomologyD (q : ℤ) :
    ({x : P // ind x = q + 1} → hM.cohomologyGrading k) →ₗ[R]
      ({y : P // ind y = q} → hM.cohomologyGrading k) :=
  LinearMap.pi fun y ↦ ∑ x, m.indexCohomologyEntry hM k (x := x.val) (y := y.val)
    (by rw [x.property, y.property]) ∘ₗ LinearMap.proj x

@[simp]
theorem indexCohomologyD_apply (q : ℤ)
    (c : {x : P // ind x = q + 1} → hM.cohomologyGrading k) (y : {y : P // ind y = q}) :
    m.indexCohomologyD hM k q c y =
      ∑ x, m.indexCohomologyEntry hM k (x := x.val) (y := y.val)
        (by rw [x.property, y.property]) (c x) := by
  simp [indexCohomologyD]

/-- The identification of a factor of the classical complex in degree `q`, the cohomology of
`shiftedModuleComplex hM q` in degree `k - q`, with `H^k(ℳ)`. -/
private noncomputable def factorEquiv (q : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) ≃ₗ[R] hM.cohomologyGrading k :=
  shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q) ≪≫ₗ
    LinearEquiv.ofEq _ _ (by rw [sub_add_cancel])

@[simp]
private theorem coe_factorEquiv_apply (q : ℤ)
    (z : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) :
    (factorEquiv.{uR, uA, uM, uP} hM k q z : hM.Cohomology) =
      shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q) z := by
  rw [factorEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]

/-- The degree-`q` term of the classical complex is the module of families indexed by the
generators of index `q` with values in `H^k(ℳ)`, through the identifications
`shiftedModuleComplexHomologyEquiv` of its factors with `H^k(ℳ)`. -/
noncomputable def indexClassicalComplexXIsoPi (q : ℤ) :
    (m.indexClassicalComplex hM k).X q ≅
      ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k) :=
  m.indexClassicalComplexXIso hM k q ≪≫ ModuleCat.piIsoPi _ ≪≫
    (LinearEquiv.piCongrRight fun _ ↦ factorEquiv.{uR, uA, uM, uP} hM k q).toModuleIso

/-- The component at a generator `x` of the identification `indexClassicalComplexXIsoPi` is the
identification `shiftedModuleComplexHomologyEquiv` of the factor at `x`. -/
theorem coe_indexClassicalComplexXIsoPi_hom_apply (q : ℤ)
    (c : (m.indexClassicalComplex hM k).X q) (x : {x : P // ind x = q}) :
    ((m.indexClassicalComplexXIsoPi hM k q).hom c x : hM.Cohomology) =
      shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q)
        ((Pi.π (fun _ : {x : P // ind x = q} ↦
          (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) x).hom
            ((m.indexClassicalComplexXIso hM k q).hom c)) := by
  simp only [indexClassicalComplexXIsoPi, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
    LinearEquiv.piCongrRight_apply, coe_factorEquiv_apply]
  exact congrArg
    (fun z ↦ (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q) z : hM.Cohomology))
    (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ModuleCat.piIsoPi_hom_ker_subtype _ x)) _)

/-- **The differential of the classical complex on families in `H^k(ℳ)`**: under the
identifications `indexClassicalComplexXIsoPi`, the differential of the classical complex is
`indexCohomologyD`. -/
theorem indexClassicalComplexXIsoPi_hom_comp_indexCohomologyD (q : ℤ) :
    (m.indexClassicalComplexXIsoPi hM k (q + 1)).hom ≫ ModuleCat.ofHom (m.indexCohomologyD hM k q) =
      (m.indexClassicalComplex hM k).d (q + 1) q ≫ (m.indexClassicalComplexXIsoPi hM k q).hom := by
  have hd := m.indexClassicalComplexXIso_inv_comp_d_comp_hom hM k q
  rw [Iso.inv_comp_eq] at hd
  have hd' := fun z ↦ LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hd) z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd'
  rw [← cancel_epi (m.indexClassicalComplexXIso hM k (q + 1)).inv]
  ext c y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    indexCohomologyD_apply, Submodule.coe_sum, coe_indexCohomologyEntry_apply]
  rw [coe_indexClassicalComplexXIsoPi_hom_apply, hd', Iso.inv_hom_id_apply]
  have hπ := m.shiftedModuleComplexHomologyEquiv_indexClassicalD_π hM k q y c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ
  rw [hπ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [coe_indexClassicalComplexXIsoPi_hom_apply, Iso.inv_hom_id_apply]

/-- **The classical differential on families in `H^k(ℳ)` squares to zero.** -/
theorem indexCohomologyD_comp_indexCohomologyD (q : ℤ) :
    m.indexCohomologyD hM k q ∘ₗ m.indexCohomologyD hM k (q + 1) = 0 := by
  have h₁ := m.indexClassicalComplexXIsoPi_hom_comp_indexCohomologyD hM k (q + 1)
  have h₂ := m.indexClassicalComplexXIsoPi_hom_comp_indexCohomologyD hM k q
  rw [← Iso.eq_inv_comp] at h₁
  rw [← Iso.eq_inv_comp] at h₂
  have h₃ : ModuleCat.ofHom (m.indexCohomologyD hM k q ∘ₗ m.indexCohomologyD hM k (q + 1)) = 0 := by
    rw [ModuleCat.ofHom_comp, h₁, h₂]
    simp
  simpa using congrArg ModuleCat.Hom.hom h₃

/-- **The classical complex on the cohomology of the module** in coefficient degree `k`: in degree
`q`, the families indexed by the generators of index `q` with values in `H^k(ℳ)`, with the
differential `indexCohomologyD`, the matrix of the actions of `(-1)^k` times the classes of the
entries `m x y` in `H⁰(A)`. It is isomorphic to the classical complex `indexClassicalComplex`
(`indexClassicalComplexIso`). -/
-- The body is exposed so that the terms of the complex are, by definition, the modules of
-- families, on which consumers compute.
@[expose]
noncomputable def indexCohomologyComplex : ChainComplex (ModuleCat.{max uM uP} R) ℤ :=
  ChainComplex.of (fun q ↦ ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k))
    (fun q ↦ ModuleCat.ofHom (m.indexCohomologyD hM k q)) fun q ↦ by
      rw [← ModuleCat.ofHom_comp, m.indexCohomologyD_comp_indexCohomologyD hM k q,
        ModuleCat.ofHom_zero]

@[simp]
theorem indexCohomologyComplex_X (q : ℤ) :
    (m.indexCohomologyComplex hM k).X q =
      ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k) :=
  (rfl)

@[simp]
theorem indexCohomologyComplex_d (q : ℤ) :
    (m.indexCohomologyComplex hM k).d (q + 1) q = ModuleCat.ofHom (m.indexCohomologyD hM k q) := by
  simp only [indexCohomologyComplex, ChainComplex.of_d]

/-- **The classical complex is the complex of families in `H^k(ℳ)`**: the classical complex in
coefficient degree `k`, whose terms are products of cohomology objects of shifted complexes, is
isomorphic to `indexCohomologyComplex`, whose terms are families indexed by the generators with
values in `H^k(ℳ)` and whose differential is the matrix of the actions of the classes of the
entries of index difference one of the twisting cocycle. -/
noncomputable def indexClassicalComplexIso :
    m.indexClassicalComplex hM k ≅ m.indexCohomologyComplex hM k :=
  HomologicalComplex.Hom.isoOfComponents (m.indexClassicalComplexXIsoPi hM k) <| by
    rintro _ q rfl
    rw [indexCohomologyComplex_d]
    exact m.indexClassicalComplexXIsoPi_hom_comp_indexCohomologyD hM k q

@[simp]
theorem indexClassicalComplexIso_hom_f (q : ℤ) :
    (m.indexClassicalComplexIso hM k).hom.f q = (m.indexClassicalComplexXIsoPi hM k q).hom :=
  (rfl)

@[simp]
theorem indexClassicalComplexIso_inv_f (q : ℤ) :
    (m.indexClassicalComplexIso hM k).inv.f q = (m.indexClassicalComplexXIsoPi hM k q).inv :=
  (rfl)

section Page

variable [DecidableEq P]

/-- **The second page of the index spectral sequence with coefficients in `H(ℳ)`**: the object at
`(a, b)` of the page `3` of the index spectral sequence (the classical `E₂` page, in Mathlib's
numbering of pages) is the homology in degree `b + 1` of the complex of families with values in
`H^{a + 2b + 1}(ℳ)` whose differential is the matrix of the actions of the classes of the entries
of the twisting cocycle. -/
noncomputable def indexSpectralSequenceSecondPageXIsoCohomology (a b : ℤ) :
    ((m.indexSpectralSequence dM hM).page 3).X (a, b) ≅
      (m.indexCohomologyComplex hM (a + 2 * b + 1)).homology (b + 1) :=
  m.indexSpectralSequenceSecondPageXIso hM a b ≪≫
    HomologicalComplex.homologyMapIso (m.indexClassicalComplexIso hM (a + 2 * b + 1)) (b + 1)

/-- The second-page isomorphism with coefficients in `H(ℳ)` is the second-page isomorphism
`indexSpectralSequenceSecondPageXIso` followed by the homology isomorphism of
`indexClassicalComplexIso`. -/
theorem indexSpectralSequenceSecondPageXIsoCohomology_eq (a b : ℤ) :
    m.indexSpectralSequenceSecondPageXIsoCohomology hM a b =
      m.indexSpectralSequenceSecondPageXIso hM a b ≪≫
        HomologicalComplex.homologyMapIso (m.indexClassicalComplexIso hM (a + 2 * b + 1))
          (b + 1) :=
  (rfl)

end Page

end TwistingCocycle

end TauCeti
