/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KoszulComplex.Basic
public import TauCeti.Algebra.Homology.Kronecker

/-!
# Koszul cohomology with module coefficients

For a linear functional `φ : M → R` and an `R`-module `N`, Koszul cohomology is the cohomology
of `Hom(K(φ), N)`. Every value of `φ` annihilates this cohomology, in every degree. In particular,
for a finite sequence generating an ideal `I`, its Koszul cohomology is annihilated by `I`.
This is the torsion input used to compare Koszul cohomology under formal glueing.

In degree one, a linear map `g : M → N` is a cocycle precisely when
`φ(m) • g(n) = φ(n) • g(m)`. Its class vanishes precisely when it has the form
`g(m) = φ(m) • z` for a single `z : N`. For `M = Rⁿ` these are the usual tuple descriptions.
We use the existing Koszul and Hom complexes, not a separate cohomology carrier.

## References

* The Stacks Project, Lemmas 15.91.6 and 15.91.7 (Tags 05EE and 05EF), for the degree-one
  cocycle description and annihilation, respectively.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (φ : Module.Dual R M) (N : ModuleCat.{max u v} R)

namespace koszulComplex

/-- Every value of the functional annihilates Koszul cohomology with arbitrary coefficients,
in every degree. -/
theorem smul_cohomology_eq_zero (m : M) (n : ℕ)
    (z : ((koszulComplex φ).linearYonedaObj R N).homology n) : φ m • z = 0 := by
  have hco : Homotopy (φ m • 𝟙 ((koszulComplex φ).linearYonedaObj R N)) 0 := by
    have h := (smulHomotopy φ m).linearYonedaFunctorMap R N
    -- The functorial presentation of Hom has the same components; identify its endpoints
    -- with the scalar and zero maps on `linearYonedaObj`.
    refine { hom := h.hom, zero := h.zero, comm := fun i ↦ ?_ }
    convert! h.comm i using 1
    · ext (f : (koszulComplex φ).X i ⟶ N) : 2
      erw [ChainComplex.linearYonedaFunctor_map_f_hom_apply]
      simp
      rfl
    · simp only [dNext, prevD, op_zero, Functor.map_zero, zero_f, add_zero]
      rfl
  have h := hco.homologyMap_eq n
  rw [HomologicalComplex.homologyMap_smul, homologyMap_id, homologyMap_zero] at h
  simpa using congr(($h).hom z)

/-- The image ideal of the functional annihilates Koszul cohomology. -/
theorem range_le_annihilator_cohomology (n : ℕ) :
    LinearMap.range φ ≤
      Module.annihilator R (((koszulComplex φ).linearYonedaObj R N).homology n) := by
  rintro _ ⟨m, rfl⟩
  exact Module.mem_annihilator.mpr (smul_cohomology_eq_zero φ N m n)

/-- Koszul cohomology of a finite sequence is annihilated by the ideal it generates.
In degree one this is Stacks, Lemma 15.91.7 (05EF). -/
@[stacks 05EF "all cohomological degrees, using Hom of the Koszul complex"]
theorem span_le_annihilator_cohomology {ι : Type v} [Fintype ι] (x : ι → R) (n : ℕ) :
    Ideal.span (Set.range x) ≤ Module.annihilator R
      (((koszulComplex (Fintype.linearCombination R x)).linearYonedaObj R N).homology n) := by
  simpa only [Fintype.range_linearCombination, Ideal.submodule_span_eq] using
    range_le_annihilator_cohomology (Fintype.linearCombination R x) N n

end koszulComplex

end TauCeti

namespace LinearMap

open TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {N : ModuleCat.{max u v} R}

/-- A degree-one Koszul cochain is closed exactly when its values satisfy the Koszul
commutation relations. -/
theorem comp_koszulDifferential_one_eq_zero_iff (g : M →ₗ[R] N) {φ : Module.Dual R M} :
    g.comp ((exteriorPower.oneEquiv R M).toLinearMap.comp (koszulDifferential φ 1)) = 0 ↔
      ∀ m n, φ m • g n = φ n • g m := by
  constructor
  · intro h m n
    have he := congrArg (fun f : ⋀[R]^2 M →ₗ[R] N ↦
      f (exteriorPower.ιMulti R 2 ![m, n])) h
    simpa [koszulDifferential_ιMulti, Fin.sum_univ_two, Fin.removeNth,
      Fin.one_succAbove_zero, sub_eq_zero, ← sub_eq_add_neg] using he
  · intro h
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa [koszulDifferential_ιMulti, Fin.sum_univ_two, Fin.removeNth,
      Fin.one_succAbove_zero, Fin.tail, ← sub_eq_add_neg] using
      sub_eq_zero.mpr (h (v 0) (v 1))

/-- The degree-one Koszul cocycle associated to a linear map satisfying the Koszul
commutation relations, in the existing Hom cochain complex. -/
def koszulCocycleOne (g : M →ₗ[R] N) {φ : Module.Dual R M}
    (hg : ∀ m n, φ m • g n = φ n • g m) :
    ((koszulComplex φ).linearYonedaObj R N).cycles 1 :=
  ChainComplex.cocycleOfComp R N
    (ModuleCat.ofHom (X := ⋀[R]^1 M)
      (g.comp (exteriorPower.oneEquiv R M).toLinearMap)) (by
      rw [(ComplexShape.up ℕ).next_eq' (by rfl : (ComplexShape.up ℕ).Rel 1 2),
        koszulComplex_d]
      exact ModuleCat.hom_ext ((comp_koszulDifferential_one_eq_zero_iff g).mpr hg)) (𝟙 N)

/-- The underlying cochain of `koszulCocycleOne` is the given linear map under `⋀¹ M ≃ M`. -/
@[simp]
theorem iCycles_koszulCocycleOne (g : M →ₗ[R] N) {φ : Module.Dual R M}
    (hg : ∀ m n, φ m • g n = φ n • g m) :
    ((koszulComplex φ).linearYonedaObj R N).iCycles 1 (koszulCocycleOne (φ := φ) g hg) =
      ModuleCat.ofHom (X := ⋀[R]^1 M)
        (g.comp (exteriorPower.oneEquiv R M).toLinearMap) := by
  dsimp only [koszulCocycleOne]
  erw [ChainComplex.iCycles_cocycleOfComp]
  exact Category.comp_id _

/-- A degree-one Koszul cocycle represents zero precisely when it is a coboundary:
its values are scalar multiples of a single coefficient vector. -/
theorem homologyπ_koszulCocycleOne_eq_zero_iff (g : M →ₗ[R] N) {φ : Module.Dual R M}
    (hg : ∀ m n, φ m • g n = φ n • g m) :
    ((koszulComplex φ).linearYonedaObj R N).homologyπ 1
        (koszulCocycleOne (φ := φ) g hg) = 0 ↔
      ∃ z : N, ∀ m, g m = φ m • z := by
  let C := (koszulComplex φ).linearYonedaObj R N
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk _ _ (C.toCycles_comp_homologyπ 0 1))
      (C.homologyIsCokernel 0 1 (by simp)))
  constructor
  · intro hzero
    obtain ⟨α, ha⟩ := hex _ hzero
    -- Give the degree-zero cochain its morphism type to use the Hom-complex API.
    obtain ⟨a, rfl⟩ : ∃ a : ModuleCat.of R (⋀[R]^0 M) ⟶ N, a = α := ⟨α, rfl⟩
    have hco := congrArg (fun c ↦ C.iCycles 1 c) ha
    dsimp only [C] at hco
    erw [ChainComplex.linearYonedaObj_iCycles_toCycles_apply,
      iCycles_koszulCocycleOne] at hco
    have hco' : ModuleCat.ofHom (koszulDifferential φ 0) ≫ a =
        ModuleCat.ofHom (g.comp (exteriorPower.oneEquiv R M).toLinearMap) := by
      rw [koszulComplex_d] at hco
      exact hco
    refine ⟨a.hom ((exteriorPower.zeroEquiv R M).symm 1), fun m ↦ ?_⟩
    have he := congr(($hco').hom ((exteriorPower.oneEquiv R M).symm m))
    have hd : koszulDifferential φ 0 ((exteriorPower.oneEquiv R M).symm m) =
        φ m • (exteriorPower.zeroEquiv R M).symm 1 := by
      apply (exteriorPower.zeroEquiv R M).injective
      simp
    simpa [hd] using he.symm
  · rintro ⟨z, hz⟩
    let a : ModuleCat.of R (⋀[R]^0 M) ⟶ N :=
      ModuleCat.ofHom (X := ⋀[R]^0 M)
        ((LinearMap.toSpanSingleton R N z).comp (exteriorPower.zeroEquiv R M).toLinearMap)
    have ha : C.toCycles 0 1 a = koszulCocycleOne (φ := φ) g hg := by
      apply HomologicalComplex.moduleCat_iCycles_injective C 1
      dsimp only [C]
      erw [ChainComplex.linearYonedaObj_iCycles_toCycles_apply, iCycles_koszulCocycleOne]
      have hco : ModuleCat.ofHom (koszulDifferential φ 0) ≫ a =
          ModuleCat.ofHom (g.comp (exteriorPower.oneEquiv R M).toLinearMap) := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simpa [a] using (hz (exteriorPower.oneEquiv R M x)).symm
      rw [koszulComplex_d]
      exact hco
    rw [← ha]
    exact ChainComplex.linearYonedaObj_homologyπ_toCycles_apply (X := koszulComplex φ)
      (k := R) (Y := N) 0 1 a

end LinearMap

namespace TauCeti.koszulComplex

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {φ : Module.Dual R M} {N : ModuleCat.{max u v} R}

/-- Every degree-one Koszul cocycle comes from a linear map satisfying the Koszul
commutation relations. -/
theorem exists_koszulCocycleOne_eq (c : ((koszulComplex φ).linearYonedaObj R N).cycles 1) :
    ∃ (g : M →ₗ[R] N) (hg : ∀ m n, φ m • g n = φ n • g m),
      LinearMap.koszulCocycleOne g hg = c := by
  let f : ModuleCat.of R (⋀[R]^1 M) ⟶ N :=
    ((koszulComplex φ).linearYonedaObj R N).iCycles 1 c
  let g : M →ₗ[R] N := f.hom.comp (exteriorPower.oneEquiv R M).symm.toLinearMap
  have hclosed : (koszulComplex φ).d 2 1 ≫ f = 0 :=
    ChainComplex.d_comp_linearYonedaObj_iCycles (k := R) (Y := N) 1 2 c
  rw [koszulComplex_d] at hclosed
  have hg : ∀ m n, φ m • g n = φ n • g m := by
    apply (LinearMap.comp_koszulDifferential_one_eq_zero_iff g).mp
    have hclosed' : ModuleCat.ofHom (koszulDifferential φ 1) ≫ f = 0 := hclosed
    have he := congrArg ModuleCat.Hom.hom hclosed'
    simpa [g, LinearMap.comp_assoc] using he
  refine ⟨g, hg, ?_⟩
  apply HomologicalComplex.moduleCat_iCycles_injective
  erw [LinearMap.iCycles_koszulCocycleOne]
  apply ModuleCat.hom_ext
  simp [g, LinearMap.comp_assoc, f]

/-- A nonunit gives a nonzero degree-one Koszul cohomology class with ring coefficients. -/
example {A : Type u} [CommRing A] {a : A} (ha : ¬ IsUnit a) :
    ∃ c : ((koszulComplex (LinearMap.toSpanSingleton A A a)).linearYonedaObj A
      (ModuleCat.of A A)).cycles 1,
      ((koszulComplex (LinearMap.toSpanSingleton A A a)).linearYonedaObj A
        (ModuleCat.of A A)).homologyπ 1 c ≠ 0 := by
  let φ := LinearMap.toSpanSingleton A A a
  let g : A →ₗ[A] (ModuleCat.of A A) := LinearMap.id
  have hg : ∀ m n, φ m • g n = φ n • g m := by
    intro m n
    simp [φ, g, mul_comm, mul_left_comm]
  refine ⟨LinearMap.koszulCocycleOne (φ := φ) g hg, fun hc ↦ ?_⟩
  obtain ⟨z, hz⟩ := (LinearMap.homologyπ_koszulCocycleOne_eq_zero_iff g hg).mp hc
  exact ha (IsUnit.of_mul_eq_one z (by simpa [φ, g] using (hz 1).symm))

end TauCeti.koszulComplex
