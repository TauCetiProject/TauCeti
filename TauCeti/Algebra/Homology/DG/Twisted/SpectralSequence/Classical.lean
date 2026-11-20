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

It then rebuilds the classical complex from `H^k(ℳ)` alone. The complex
`TauCeti.TwistingCocycle.indexClassicalCohomologyComplex` has in degree `q` the families, indexed by
the generators of index `q`, of classes in `H^k(ℳ)`, and as differential
`c ↦ (y ↦ (-1)^k ∑ₓ c x · [m x y])`, the matrix of the right actions on `H^k(ℳ)` of the classes in
`H⁰(A)` of the entries of the cocycle. It is isomorphic to the classical complex
(`TauCeti.TwistingCocycle.indexClassicalComplexIso`), so the second page of the index spectral
sequence is its homology (`TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIsoCohomology`):
`E²` is the homology of the generators with coefficients in the cohomology of `ℳ`, acted on by
`H⁰(A)` through the degree-zero entries of the cocycle.

## Main definitions

* `TauCeti.TwistingCocycle.indexClassicalClass`: the class in `H(A)` of an entry of index
  difference one.
* `TauCeti.TwistingCocycle.indexClassicalAction`: its action on `H^k(ℳ)`.
* `TauCeti.TwistingCocycle.indexClassicalCohomologyComplex`: the classical complex with
  coefficients in `H^k(ℳ)`, with differential `TauCeti.TwistingCocycle.indexClassicalCohomologyD`.
* `TauCeti.TwistingCocycle.indexClassicalComplexIso`: the isomorphism of the classical complex with
  `indexClassicalCohomologyComplex`.
* `TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIsoCohomology`: the second page of the
  index spectral sequence is the homology of `indexClassicalCohomologyComplex`.

## Main results

* `TauCeti.TwistingCocycle.indexClassicalClass_mem_cohomologyGrading_zero`: this class lies in
  `H⁰(A)`.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`: the entries of
  the classical complex are `(-1)^k` times the actions of the classes of the entries of the
  twisting cocycle.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalD_π`: the components of
  the classical differential are `(-1)^k` times the sums of these actions.
* `TauCeti.TwistingCocycle.indexClassicalD_comp_indexClassicalProdIsoPi_hom`: under the
  identifications `indexClassicalProdIsoPi` of the terms with families of classes in
  `H^k(ℳ)`, the classical differential is `indexClassicalCohomologyD`.

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

/-! ### The classical complex with coefficients in `H^k(ℳ)` -/

variable (h) in
/-- The action on `H^k(ℳ)` of the class of an entry `m x y` of index difference one. The class has
degree zero (`TauCeti.TwistingCocycle.indexClassicalClass_mem_cohomologyGrading_zero`), so its
action on the cohomology of `ℳ` preserves the degree. -/
noncomputable def indexClassicalAction {x y : P} (hxy : ind x = ind y + 1) :
    hM.cohomologyGrading k →ₗ[R] hM.cohomologyGrading k :=
  (hM.cohomologyAction (m.indexClassicalClass h hxy)).unop.restrict fun _ hc ↦ by
    simpa only [add_zero] using hM.cohomologyAction_apply_mem_cohomologyGrading
      (m.indexClassicalClass_mem_cohomologyGrading_zero h hxy) hc

variable (h) in
@[simp]
theorem coe_indexClassicalAction_apply {x y : P} (hxy : ind x = ind y + 1)
    (c : hM.cohomologyGrading k) :
    (m.indexClassicalAction h hM k hxy c : hM.Cohomology) =
      (hM.cohomologyAction (m.indexClassicalClass h hxy)).unop c :=
  (rfl)

/-- The differential of the classical complex with coefficients in `H^k(ℳ)`: a family `c` indexed
by the generators of index `q + 1` goes to the family whose component at a generator `y` of index
`q` is `(-1)^k ∑ₓ c x · [m x y]`. -/
noncomputable def indexClassicalCohomologyD (q : ℤ) :
    ({x : P // ind x = q + 1} → hM.cohomologyGrading k) →ₗ[R]
      ({y : P // ind y = q} → hM.cohomologyGrading k) :=
  LinearMap.pi fun y ↦ (k.negOnePow : ℤ) • ∑ x : {x : P // ind x = q + 1},
    (m.indexClassicalAction h hM k (x := x.1) (y := y.1) (by rw [x.2, y.2])).comp
      (LinearMap.proj x)

@[simp]
theorem indexClassicalCohomologyD_apply (q : ℤ)
    (c : {x : P // ind x = q + 1} → hM.cohomologyGrading k) (y : {y : P // ind y = q}) :
    m.indexClassicalCohomologyD hM k q c y = (k.negOnePow : ℤ) • ∑ x : {x : P // ind x = q + 1},
      m.indexClassicalAction h hM k (x := x.1) (y := y.1) (by rw [x.2, y.2]) (c x) := by
  simp [indexClassicalCohomologyD]

omit [Fintype P] in
/-- The terms of the classical complex in coefficient degree `k` are products of copies of
`H^k(ℳ)`: the product over the generators of index `q` of the cohomology of
`shiftedModuleComplex hM q` in degree `k - q` is the module of families of classes in `H^k(ℳ)`,
through `TauCeti.shiftedModuleComplexHomologyEquiv` in each factor. -/
noncomputable def indexClassicalProdIsoPi (q : ℤ) :
    (∏ᶜ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) ≅
      ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k) :=
  ModuleCat.piIsoPi _ ≪≫ (LinearEquiv.piCongrRight fun _ ↦
    shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q) ≪≫ₗ
      LinearEquiv.ofEq _ _ (by rw [sub_add_cancel])).toModuleIso

omit [Fintype P] in
@[simp]
theorem coe_indexClassicalProdIsoPi_hom_apply (q : ℤ)
    (c : ↑(∏ᶜ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)))
    (x : {x : P // ind x = q}) :
    ((indexClassicalProdIsoPi hM k q).hom.hom c x : hM.Cohomology) =
      shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q)
        ((Pi.π (fun _ : {x : P // ind x = q} ↦
          (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) x).hom c) := by
  have := congrArg (fun f ↦ f.hom c) (ModuleCat.piIsoPi_hom_ker_subtype
    (fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) x)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.proj_apply] at this
  simp [indexClassicalProdIsoPi, this]

/-- **The classical differential on families of classes in `H^k(ℳ)`**: under the identifications
`indexClassicalProdIsoPi` of the terms of the classical complex with families of classes
in `H^k(ℳ)`, the classical differential `indexClassicalD` is `indexClassicalCohomologyD`. -/
@[reassoc]
theorem indexClassicalD_comp_indexClassicalProdIsoPi_hom (q : ℤ) :
    m.indexClassicalD hM k q ≫ (indexClassicalProdIsoPi hM k q).hom =
      (indexClassicalProdIsoPi hM k (q + 1)).hom ≫
        ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q) := by
  ext c : 2
  funext y
  apply Subtype.ext
  have hπ := m.shiftedModuleComplexHomologyEquiv_indexClassicalD_π hM k q y c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ ⊢
  rw [coe_indexClassicalProdIsoPi_hom_apply, hπ, ModuleCat.hom_ofHom,
    indexClassicalCohomologyD_apply, Units.smul_def]
  -- Push the coercion `H^k(ℳ) → H(ℳ)`, the linear map `Submodule.subtype`, through the integer
  -- multiple and the sum; the coercion lemmas for submodules do not apply to these instances.
  conv_rhs => rw [← Submodule.subtype_apply, map_zsmul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun x _ ↦ ?_)
  rw [Submodule.subtype_apply, coe_indexClassicalAction_apply,
    coe_indexClassicalProdIsoPi_hom_apply]

/-- `indexClassicalCohomologyD` is the classical differential `indexClassicalD`, transported along
the identifications `indexClassicalProdIsoPi`. -/
theorem indexClassicalCohomologyD_eq (q : ℤ) :
    ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q) =
      (indexClassicalProdIsoPi hM k (q + 1)).inv ≫ m.indexClassicalD hM k q ≫
        (indexClassicalProdIsoPi hM k q).hom := by
  rw [indexClassicalD_comp_indexClassicalProdIsoPi_hom, Iso.inv_hom_id_assoc]

/-- The differential `indexClassicalCohomologyD` squares to zero, since the classical differential
does (`TauCeti.TwistingCocycle.indexClassicalD_comp`). -/
theorem indexClassicalCohomologyD_comp (q : ℤ) :
    ModuleCat.ofHom (m.indexClassicalCohomologyD hM k (q + 1)) ≫
      ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q) = 0 := by
  simp [indexClassicalCohomologyD_eq, reassoc_of% m.indexClassicalD_comp hM k q]

/-- **The classical complex with coefficients in `H^k(ℳ)`**: in degree `q` the families, indexed
by the generators of index `q`, of classes in the cohomology `H^k(ℳ)`, with the differential
`(-1)^k ∑ₓ c x · [m x y]` given by the right action of the classes in `H⁰(A)` of the entries of
the twisting cocycle (`TauCeti.TwistingCocycle.indexClassicalCohomologyD`). It is isomorphic to
the classical complex `TauCeti.TwistingCocycle.indexClassicalComplex`
(`TauCeti.TwistingCocycle.indexClassicalComplexIso`). -/
noncomputable def indexClassicalCohomologyComplex :
    ChainComplex (ModuleCat.{max uM uP} R) ℤ :=
  ChainComplex.of (fun q ↦ ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k))
    (fun q ↦ ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q))
    (m.indexClassicalCohomologyD_comp hM k)

/-- The degree-`q` term of the classical complex with coefficients in `H^k(ℳ)` is the module of
families of classes in `H^k(ℳ)` indexed by the generators of index `q`. -/
noncomputable def indexClassicalCohomologyComplexXIso (q : ℤ) :
    (m.indexClassicalCohomologyComplex hM k).X q ≅
      ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k) :=
  -- The terms of `ChainComplex.of` are the given family of objects.
  Iso.refl _

private theorem indexClassicalCohomologyComplex_d_eq (q : ℤ) :
    (m.indexClassicalCohomologyComplex hM k).d (q + 1) q =
      ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q) := by
  unfold indexClassicalCohomologyComplex
  exact ChainComplex.of_d
    (fun q ↦ ModuleCat.of R ({x : P // ind x = q} → hM.cohomologyGrading k))
    (fun q ↦ ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q)) q

/-- **The differential of the classical complex with coefficients in `H^k(ℳ)` is
`indexClassicalCohomologyD`**, under the identification `indexClassicalCohomologyComplexXIso` of
its terms. -/
theorem indexClassicalCohomologyComplexXIso_inv_comp_d_comp_hom (q : ℤ) :
    (m.indexClassicalCohomologyComplexXIso hM k (q + 1)).inv ≫
      (m.indexClassicalCohomologyComplex hM k).d (q + 1) q ≫
        (m.indexClassicalCohomologyComplexXIso hM k q).hom =
      ModuleCat.ofHom (m.indexClassicalCohomologyD hM k q) := by
  rw [indexClassicalCohomologyComplex_d_eq]
  -- Both identifications are the identity, by definition of
  -- `indexClassicalCohomologyComplexXIso`.
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- **The classical complex is the complex of families of classes in `H^k(ℳ)`**: the classical
complex in coefficient degree `k`, whose homology is the second page of the index spectral
sequence, is isomorphic to `indexClassicalCohomologyComplex`, whose terms are families of classes
in `H^k(ℳ)` indexed by the generators and whose differential is the action of the classes of the
entries of the twisting cocycle. -/
noncomputable def indexClassicalComplexIso :
    m.indexClassicalComplex hM k ≅ m.indexClassicalCohomologyComplex hM k :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ m.indexClassicalComplexXIso hM k q ≪≫ indexClassicalProdIsoPi hM k q ≪≫
      (m.indexClassicalCohomologyComplexXIso hM k q).symm) <| by
    rintro _ q rfl
    rw [← cancel_epi (m.indexClassicalComplexXIso hM k (q + 1)).inv,
      ← cancel_mono (m.indexClassicalCohomologyComplexXIso hM k q).hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, indexClassicalCohomologyComplexXIso_inv_comp_d_comp_hom,
      ← indexClassicalD_comp_indexClassicalProdIsoPi_hom,
      reassoc_of% m.indexClassicalComplexXIso_inv_comp_d_comp_hom hM k q]

/-- The component in degree `q` of `indexClassicalComplexIso` is `indexClassicalProdIsoPi`,
under the identifications of the terms of the two complexes. -/
theorem indexClassicalComplexIso_hom_f (q : ℤ) :
    (m.indexClassicalComplexIso hM k).hom.f q =
      (m.indexClassicalComplexXIso hM k q).hom ≫ (indexClassicalProdIsoPi hM k q).hom ≫
        (m.indexClassicalCohomologyComplexXIso hM k q).inv := by
  simp [indexClassicalComplexIso]

section Page

variable [DecidableEq P]

/-- **The second page of the index spectral sequence is the homology of the classical complex
with coefficients in `H^k(ℳ)`**, for `k = a + 2 * b + 1`: the object at `(a, b)` of the page `3`
(the classical `E₂` page, in Mathlib's numbering of pages) is the homology in degree
`b + 1` of `indexClassicalCohomologyComplex` in coefficient degree `a + 2 * b + 1`, the complex of
families of classes in `H^(a + 2 * b + 1)(ℳ)` indexed by the generators. -/
noncomputable def indexSpectralSequenceSecondPageXIsoCohomology (a b : ℤ) :
    ((m.indexSpectralSequence dM hM).page 3).X (a, b) ≅
      (m.indexClassicalCohomologyComplex hM (a + 2 * b + 1)).homology (b + 1) :=
  m.indexSpectralSequenceSecondPageXIso hM a b ≪≫
    HomologicalComplex.homologyMapIso (m.indexClassicalComplexIso hM _) _

end Page

end TwistingCocycle

end TauCeti
