/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.E2
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology

/-!
# The classical complex on the cohomology of a DG module

The second page of the index spectral sequence of a twisted complex is the cohomology of the
classical complex `TauCeti.TwistingCocycle.indexClassicalComplex`, whose terms are products of the
cohomology of `shiftedModuleComplex hM q`, a reindexing of the complex of a DG right module `ℳ`,
and whose entries are the actions of the cycles `m x y` of degree zero. This file identifies these
terms and entries with the intrinsic cohomology `H(ℳ)` of the module and the action on it of the
cohomology algebra `H(A)`, through which the coefficients of the classical complex become
`H^k(ℳ)` as a module over `H⁰(A)`.

The cohomology of `shiftedModuleComplex hM p` in degree `n` is the piece `H^{n + p}(ℳ)` of
`H(ℳ)` (`TauCeti.shiftedModuleComplexHomologyEquiv`), the class of a cycle going to its class in
`H(ℳ)`. Both are the quotient of the homogeneous cycles of degree `n + p` by those that are
boundaries; a homogeneous cycle that is the differential of some element is the differential of
the homogeneous component of that element one degree lower.

Under these identifications, the action of a cycle `a` of degree zero twisted by the Koszul sign
(`TauCeti.shiftedModuleComplexActHomology`) is the action of the class of `a` in `H(A)`, with the
sign `(-1)^j` on `H^j(ℳ)`
(`TauCeti.shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology`).
So the entry of the classical complex in coefficient degree `k` between generators `x` and `y` is
`(-1)^k` times the action of the class of `m x y` on `H^k(ℳ)`
(`TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`): the classical
complex in coefficient degree `k` is the complex of the generators with coefficients in the
`H⁰(A)`-module `H^k(ℳ)`, with differential the matrix of the classes of the entries of index
difference one, up to the overall sign `(-1)^k`.

## Main definitions

* `TauCeti.shiftedModuleComplexHomologyEquiv`: the cohomology of `shiftedModuleComplex hM p` in
  degree `n` is `H^{n + p}(ℳ)`.

## Main results

* `TauCeti.shiftedModuleComplexHomologyEquiv_homologyπ`: the identification sends the class of a
  cycle to its class in `H(ℳ)`.
* `TauCeti.shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology`: the action of a
  cycle of degree zero is the action of its class on `H(ℳ)`, up to the Koszul sign.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`: the entries of
  the classical complex are the actions of the classes of the entries of the twisting cocycle.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

section Cohomology

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (hM : IsDGRightModule h ℳ dM)

/-- The value in `ℳ` of a cycle of `shiftedModuleComplex hM p` is a cycle of `ℳ`. -/
private theorem dM_shiftedModuleComplexXEquiv_iCycles (p n : ℤ)
    (z : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).cycles n) :
    dM (shiftedModuleComplexXEquiv hM p n
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).iCycles n z)) = 0 :=
  (shiftedModuleComplexXEquiv_d_eq_zero_iff hM p n _).1
    ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCat_d_iCycles_apply n (n + 1) z)

/-- The class in `H^{n + p}(ℳ)` of the value in `ℳ` of a cycle of `shiftedModuleComplex hM p` of
degree `n`. -/
private noncomputable def cyclesToCohomologyGrading (p n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM p).cycles n →ₗ[R] hM.cohomologyGrading (n + p) where
  toFun z := ⟨Submodule.Quotient.mk ⟨shiftedModuleComplexXEquiv hM p n
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).iCycles n z),
        hM.mem_cycles.mpr (dM_shiftedModuleComplexXEquiv_iCycles hM p n z)⟩,
    hM.quotientMk_mem_cohomologyGrading (shiftedModuleComplexXEquiv hM p n _).2⟩
  map_add' z w := by
    apply Subtype.ext
    rw [Submodule.coe_add, ← Submodule.Quotient.mk_add]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    simp only [map_add, Submodule.coe_add]
  map_smul' r z := by
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    simp only [map_smul, Submodule.coe_smul_of_tower]

private theorem cyclesToCohomologyGrading_apply (p n : ℤ)
    (z : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).cycles n) :
    (cyclesToCohomologyGrading.{uR, uA, uM, uP} hM p n z : hM.Cohomology) =
      Submodule.Quotient.mk ⟨shiftedModuleComplexXEquiv hM p n
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).iCycles n z),
          hM.mem_cycles.mpr (dM_shiftedModuleComplexXEquiv_iCycles hM p n z)⟩ :=
  (rfl)

private theorem cyclesToCohomologyGrading_surjective (p n : ℤ) :
    Function.Surjective (cyclesToCohomologyGrading.{uR, uA, uM, uP} hM p n) := by
  rintro ⟨x, hx⟩
  obtain ⟨z, hz, rfl⟩ := hM.mem_cohomologyGrading.mp hx
  set α := (shiftedModuleComplexXEquiv hM p n).symm ⟨z, hz⟩
  have hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).d n (n + 1)).hom α = 0 := by
    rw [shiftedModuleComplexXEquiv_d_eq_zero_iff, LinearEquiv.apply_symm_apply]
    exact hM.mem_cycles.mp z.2
  refine ⟨(shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCatCyclesMk α (n + 1) (by simp) hα,
    Subtype.ext ?_⟩
  rw [cyclesToCohomologyGrading_apply]
  congr 1
  ext
  simp [α]

/-- A cycle of `shiftedModuleComplex hM p` has zero class exactly when its value in `ℳ` is a
boundary: a homogeneous boundary is the differential of an element one degree lower. -/
private theorem ker_homologyπ_shiftedModuleComplex (p n : ℤ) :
    LinearMap.ker ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).homologyπ n).hom =
      LinearMap.ker (cyclesToCohomologyGrading.{uR, uA, uM, uP} hM p n) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    (shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCat_homologyπ_eq_zero_iff
      (m := n - 1) (by simp),
    ← Subtype.coe_inj, cyclesToCohomologyGrading_apply, Submodule.coe_zero,
    hM.quotientMk_eq_zero_iff, hM.mem_boundaries]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨shiftedModuleComplexXEquiv hM p (n - 1) y, ?_⟩
    have hd := shiftedModuleComplexXEquiv_d hM p (n - 1) y
    rw [sub_add_cancel] at hd
    rw [← hd]
    simp
  · rintro ⟨x, hx⟩
    have hmem : (DirectSum.decompose ℳ x (n - 1 + p) : M) ∈ ℳ (n - 1 + p) :=
      Submodule.coe_mem _
    refine ⟨(shiftedModuleComplexXEquiv hM p (n - 1)).symm ⟨_, hmem⟩, ?_⟩
    apply (shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCat_iCycles_injective n
    apply (shiftedModuleComplexXEquiv hM p n).injective
    ext
    have hd := shiftedModuleComplexXEquiv_d hM p (n - 1)
      ((shiftedModuleComplexXEquiv hM p (n - 1)).symm ⟨_, hmem⟩)
    rw [sub_add_cancel] at hd
    rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply, hd, LinearEquiv.apply_symm_apply,
      hM.map_decompose, hx]
    have hdeg : n - 1 + p + 1 = n + p := by ring
    rw [hdeg]
    exact DirectSum.decompose_of_mem_same ℳ (shiftedModuleComplexXEquiv hM p n _).2

/-- **The cohomology of the shifted complex of a DG module is its intrinsic cohomology**: the
cohomology of `shiftedModuleComplex hM p` in degree `n` is the piece `H^{n + p}(ℳ)` of the
cohomology `H(ℳ)`, the class of a cycle going to its class in `H(ℳ)`
(`shiftedModuleComplexHomologyEquiv_homologyπ`). -/
noncomputable def shiftedModuleComplexHomologyEquiv (p n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM p).homology n ≃ₗ[R]
      hM.cohomologyGrading (n + p) :=
  (LinearMap.quotKerEquivOfSurjective _
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCat_homologyπ_surjective n)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ker_homologyπ_shiftedModuleComplex hM p n) ≪≫ₗ
    (cyclesToCohomologyGrading.{uR, uA, uM, uP} hM p n).quotKerEquivOfSurjective
      (cyclesToCohomologyGrading_surjective hM p n)

private theorem shiftedModuleComplexHomologyEquiv_homologyπ_apply (p n : ℤ)
    (z : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).cycles n) :
    shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM p n
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM p).homologyπ n).hom z) =
      cyclesToCohomologyGrading.{uR, uA, uM, uP} hM p n z := by
  rw [shiftedModuleComplexHomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    (LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ z).symm,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The identification of `shiftedModuleComplexHomologyEquiv` sends the class of a cycle `α` of
`shiftedModuleComplex hM p` to the class in `H(ℳ)` of its value in `ℳ`. -/
theorem shiftedModuleComplexHomologyEquiv_homologyπ (p n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n)
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).d n (n + 1)).hom α = 0) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM p n
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM p).homologyπ n).hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCatCyclesMk α (n + 1)
            (by simp) hα)) : hM.Cohomology) =
      Submodule.Quotient.mk (⟨shiftedModuleComplexXEquiv hM p n α,
        hM.mem_cycles.mpr ((shiftedModuleComplexXEquiv_d_eq_zero_iff hM p n α).1 hα)⟩ :
          hM.cycles) := by
  rw [shiftedModuleComplexHomologyEquiv_homologyπ_apply, cyclesToCohomologyGrading_apply]
  simp only [HomologicalComplex.iCycles_moduleCatCyclesMk]

/-- A map between the cohomologies of `shiftedModuleComplex hM (q + 1)` and
`shiftedModuleComplex hM q` which acts on classes as the action of a cycle `a` of degree zero
twisted by the Koszul sign is, under the identifications `shiftedModuleComplexHomologyEquiv`, the
action of the class of `a` multiplied by the Koszul sign. -/
private theorem shiftedModuleComplexHomologyEquiv_apply_of_homologyπ {a : A} (ha : a ∈ 𝒜 0)
    (hda : d a = 0) (q n n' : ℤ) (hn : 1 + n = n')
    (f : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology n ⟶
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology n')
    (hf : ∀ (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X n)
      (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d n (n + 1)).hom α = 0)
      (β : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X n'),
      (shiftedModuleComplexXEquiv hM q n' β : M) =
        op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
          (shiftedModuleComplexXEquiv hM (q + 1) n α : M) →
      ∀ (hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d n' (n' + 1)).hom β = 0),
      f.hom (((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homologyπ n).hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).moduleCatCyclesMk α (n + 1)
            (by simp) hα)) =
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).homologyπ n').hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCatCyclesMk β (n' + 1)
            (by simp) hβ'))
    (c : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology n) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q n' (f.hom c) : hM.Cohomology) =
      (n + (q + 1)).negOnePow • (hM.cohomologyAction
        (Ideal.Quotient.mk h.boundaries.asIdeal ⟨a, h.mem_cycles.mpr hda⟩)).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) n c) := by
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1)).exists_homologyπ_moduleCatCyclesMk_eq (n + 1) (by simp) c
  obtain ⟨β, hβ', hβ, -⟩ :=
    exists_shiftedModuleComplexActHomology_homologyπ hM ha hda q n n' hn α hα
  rw [hf α hα β hβ hβ', shiftedModuleComplexHomologyEquiv_homologyπ,
    shiftedModuleComplexHomologyEquiv_homologyπ, hM.cohomologyAction_mk,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  ext
  rw [hβ, InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _
      (shiftedModuleComplexXEquiv hM (q + 1) n α).2, one_mul, Int.cast_smul_eq_zsmul,
    Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, Units.smul_def, smul_comm]
  -- The opposite cycle `op ⟨a, _⟩` acts on `ℳ` as `op a` does, by definition of the action.
  rfl

/-- **The action of a cycle of degree zero on cohomology is the action of its class**: under the
identifications `shiftedModuleComplexHomologyEquiv`, the map
`shiftedModuleComplexActHomology` induced by a cycle `a` of degree zero, from the cohomology of
`shiftedModuleComplex hM (q + 1)` in degree `n`, which is `H^{n + q + 1}(ℳ)`, is the action of
the class of `a` in `H(A)`, multiplied by the Koszul sign `(-1)^(n + q + 1)`. -/
theorem shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology {a : A} (ha : a ∈ 𝒜 0)
    (hda : d a = 0) (q n n' : ℤ) (hn : 1 + n = n')
    (c : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology n) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q n'
        ((shiftedModuleComplexActHomology hM ha hda q n n' hn).hom c) : hM.Cohomology) =
      (n + (q + 1)).negOnePow • (hM.cohomologyAction
        (Ideal.Quotient.mk h.boundaries.asIdeal ⟨a, h.mem_cycles.mpr hda⟩)).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) n c) :=
  shiftedModuleComplexHomologyEquiv_apply_of_homologyπ hM ha hda q n n' hn _
    (shiftedModuleComplexActHomology_homologyπ hM ha hda q n n' hn) c

end Cohomology

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM) (k : ℤ)

/-- The class in the cohomology `H(A)` of the entry `m x y` between generators whose indices
differ by one, a cycle of degree zero. -/
noncomputable def indexClassicalClass {x y : P} (hxy : ind x = ind y + 1) : h.Cohomology :=
  Ideal.Quotient.mk h.boundaries.asIdeal
    ⟨m.m x y, h.mem_cycles.mpr (m.d_m_eq_zero_of_eq_add_one hxy)⟩

theorem indexClassicalClass_def {x y : P} (hxy : ind x = ind y + 1) :
    m.indexClassicalClass hxy = Ideal.Quotient.mk h.boundaries.asIdeal
      ⟨m.m x y, h.mem_cycles.mpr (m.d_m_eq_zero_of_eq_add_one hxy)⟩ :=
  (rfl)

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
        (m.indexClassicalClass (x := x.1) (y := y.1) (by rw [x.2, y.2]))).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) (k - (q + 1)) c) := by
  rw [shiftedModuleComplexHomologyEquiv_apply_of_homologyπ hM
    (m.m_mem_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2]))
    (m.d_m_eq_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2])) q (k - (q + 1))
    (k - q) (by ring) _ (m.indexClassicalEntry_homologyπ hM k q x y) c,
    show (k - (q + 1) + (q + 1)).negOnePow = k.negOnePow by rw [sub_add_cancel]]
  rfl

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
        (m.indexClassicalClass (x := x.1) (y := y.1) (by rw [x.2, y.2]))).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) (k - (q + 1))
            ((Pi.π (fun _ : {x : P // ind x = q + 1} ↦
              (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) x).hom
                c)) := by
  rw [indexClassicalD_π, ModuleCat.hom_sum, LinearMap.sum_apply, map_sum, Submodule.coe_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply,
    shiftedModuleComplexHomologyEquiv_indexClassicalEntry]

end TwistingCocycle

end TauCeti
