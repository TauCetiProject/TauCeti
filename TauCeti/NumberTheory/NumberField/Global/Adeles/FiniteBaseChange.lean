/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Extension
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact
import Mathlib.LinearAlgebra.Countable
import TauCeti.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Base change of finite adeles

For number fields `L/K`, the canonical map from `𝔸ᶠ_K ⊗[K] L` to `𝔸ᶠ_L` multiplies
an extended adele by a diagonal field element. It is an algebra equivalence over `𝔸ᶠ_K`, and a
homeomorphism when the source carries its module topology over `𝔸ᶠ_K`.

Injectivity holds because the semilocal decomposition at every finite place detects the
coordinates of a tensor in any scalar-extended field basis. For surjectivity, write the
components of a finite adele of `L` above each finite place `v` of `K` in an integral basis
`b` of `L`, as `∑ i, c_i ⊗ b_i` with `c_i ∈ K_v`. At the cofinitely many places where those
components are integral, the integral semilocal decomposition
`𝒪_v ⊗[𝓞 K] 𝓞 L ≃ ∏_{w ∣ v} 𝒪_w` lets the `c_i` be chosen in `𝒪_v`, so they assemble to
finite adeles of `K`. The inverse is continuous by the open mapping theorem for σ-compact
groups, as for the infinite-adele comparison in
`TauCeti.NumberTheory.NumberField.Global.Adeles.InfiniteBaseChange`.

## Main definitions

* `TauCeti.GlobalNumberFields.finiteAdeleBaseChangeHom`: the canonical map
  `𝔸ᶠ_K ⊗[K] L →ₐ[𝔸ᶠ_K] 𝔸ᶠ_L`.
* `TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv`: that map as an algebra
  equivalence.
* `TauCeti.GlobalNumberFields.finiteAdeleBaseChangeEquiv`: that map as a continuous algebra
  equivalence, for the module topology on the source.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleBaseChangeHom_apply`: the components above `v` are
  the semilocal map after evaluation at `v`.
* `TauCeti.GlobalNumberFields.finiteAdeleBaseChangeHom_injective`,
  `TauCeti.GlobalNumberFields.finiteAdeleBaseChangeHom_surjective`: the map is bijective.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct FiniteAdeleExtension AdicCompletionExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private local instance (priority := 50) : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

private local instance (priority := 50) : IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq' rfl

private local instance : IsScalarTower K (FiniteAdeleRing (𝓞 K) K)
    (FiniteAdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_finiteAdeleExtensionAlgebra]
    exact (finiteAdeleExtension_algebraMap (𝓞 K) K (𝓞 L) L x).symm

/-- The canonical scalar-extension map of finite adeles over the finite adele ring of the
base field. -/
def finiteAdeleBaseChangeHom :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L →ₐ[FiniteAdeleRing (𝓞 K) K]
      FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom K L (FiniteAdeleRing (𝓞 L) L)) fun _ _ ↦ .all _ _

/-- A pure tensor is sent to the extended adele times the diagonal field element. -/
@[simp]
theorem finiteAdeleBaseChangeHom_tmul (a : FiniteAdeleRing (𝓞 K) K) (x : L) :
    finiteAdeleBaseChangeHom K L (a ⊗ₜ x) =
      finiteAdeleExtension (𝓞 K) K (𝓞 L) L a *
        algebraMap L (FiniteAdeleRing (𝓞 L) L) x := by
  simp [finiteAdeleBaseChangeHom, Algebra.ofId_apply,
    algebraMap_finiteAdeleExtensionAlgebra]

/-- The component above `v` of the finite-adele comparison is the semilocal map after
scalar extension of evaluation at `v`. -/
@[simp]
theorem finiteAdeleBaseChangeHom_apply (s : FiniteAdeleRing (𝓞 K) K ⊗[K] L)
    (v : HeightOneSpectrum (𝓞 K))
    (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
    let f : FiniteAdeleRing (𝓞 K) K →ₗ[K] v.adicCompletion K :=
      { toFun := fun a ↦ a v
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun c a ↦ by
          simp only [Algebra.smul_def, RingHom.id_apply]
          rfl }
    finiteAdeleBaseChangeHom K L s w.1 =
      semilocalHom L v (TensorProduct.map f (LinearMap.id : L →ₗ[K] L) s) w := by
  intro f
  induction s using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, semilocalHom_tmul,
      finiteAdeleBaseChangeHom_tmul, FiniteAdeleRing.mul_apply,
      finiteAdeleExtension_apply, FiniteAdeleRing.algebraMap_apply]
    rcases w with ⟨w, hw⟩
    have hv : v = w.under (𝓞 K) := HeightOneSpectrum.asIdeal_injective hw.over
    subst v
    rw [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
    rfl
  | add t u ht hu =>
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) ht hu

/-- The canonical scalar-extension map of finite adeles is injective. -/
theorem finiteAdeleBaseChangeHom_injective :
    Function.Injective (finiteAdeleBaseChangeHom K L) := by
  classical
  let b := Module.finBasis K L
  let B := b.baseChange (FiniteAdeleRing (𝓞 K) K)
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  apply B.repr.injective
  apply Finsupp.ext
  intro i
  apply FiniteAdeleRing.ext
  intro v
  let f : FiniteAdeleRing (𝓞 K) K →ₗ[K] v.adicCompletion K :=
    { toFun := fun a ↦ a v
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c a ↦ by
        simp only [Algebra.smul_def, RingHom.id_apply]
        rfl }
  let T := TensorProduct.map f (LinearMap.id : L →ₗ[K] L)
  -- A zero adelic image gives a zero tensor at `v` by semilocal injectivity.
  have hT : T t = 0 := by
    apply semilocalHom_injective L v
    funext w
    rw [← finiteAdeleBaseChangeHom_apply K L t v w, ht, map_zero]
    rfl
  -- Evaluation commutes with the scalar-extended basis coordinates.
  have hcoord (s : FiniteAdeleRing (𝓞 K) K ⊗[K] L) :
      (b.baseChange (v.adicCompletion K)).repr (T s) i = B.repr s i v := by
    induction s using TensorProduct.inductionOn with
    | tmul a x =>
      simp only [T, TensorProduct.map_tmul, LinearMap.id_apply, B,
        Module.Basis.baseChange_repr_tmul]
      exact (f.map_smul ((b.repr x) i) a).symm
    | add t u ht hu =>
      simp only [map_add, Finsupp.add_apply, ht, hu]
      rfl
  rw [← hcoord, hT]
  simp

/-- At a finite place `v` of `K`, every family of components above `v` is the semilocal image of
`∑ i, c i ⊗ b i` for an integral basis `b` of `L`, with coefficients `c i ∈ K_v`. When every
component is integral, the coefficients can be chosen in `𝒪_v`. -/
private theorem exists_semilocalHom_sum_tmul_eq (v : HeightOneSpectrum (𝓞 K))
    (z : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
      w.1.adicCompletion L) :
    ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → v.adicCompletion K,
      semilocalHom L v (∑ i, c i ⊗ₜ[K] (RingOfIntegers.basis L i : L)) = z ∧
      ((∀ w, z w ∈ w.1.adicCompletionIntegers L) → ∀ i, c i ∈ v.adicCompletionIntegers K) := by
  classical
  let b := RingOfIntegers.basis L
  by_cases hz : ∀ w, z w ∈ w.1.adicCompletionIntegers L
  · -- Integral components come from the integral tensor product, which `1 ⊗ b i` spans.
    obtain ⟨ζ, hζ⟩ := (integralSemilocalEquiv L v).surjective fun w ↦ ⟨z w, hz w⟩
    have hspan : Submodule.span (v.adicCompletionIntegers K)
        (Set.range fun i ↦ (1 : v.adicCompletionIntegers K) ⊗ₜ[𝓞 K] b i) = ⊤ := by
      have h := Submodule.baseChange_span (R := 𝓞 K) (v.adicCompletionIntegers K) (Set.range b)
      rw [Submodule.span_eq_top_of_span_eq_top ℤ (𝓞 K) _ b.span_eq, Submodule.baseChange_top,
        ← Set.range_comp] at h
      exact h.symm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (hspan ▸ Submodule.mem_top : ζ ∈ Submodule.span _ _)
    refine ⟨fun i ↦ c i, ?_, fun _ i ↦ (c i).2⟩
    have h := integralSemilocalEquiv_fieldCompatibility ζ
    rw [hζ, ← hc, map_sum] at h
    simp_rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      integralSemilocalToField_tmul, coe_semilocalEquiv] at h
    exact h
  · -- Otherwise any coefficients do, since `1 ⊗ b i` spans `K_v ⊗ L` over `K_v`.
    have hspan : Submodule.span (v.adicCompletion K)
        (Set.range fun i ↦ (1 : v.adicCompletion K) ⊗ₜ[K] (b i : L)) = ⊤ := by
      have hb : Submodule.span K (Set.range fun i ↦ (b i : L)) = ⊤ := by
        refine Submodule.span_eq_top_of_span_eq_top ℚ K _ ?_
        rw [← (integralBasis L).span_eq]
        exact congrArg _ (congrArg Set.range (funext fun i ↦ (integralBasis_apply L i).symm))
      have h := Submodule.baseChange_span (R := K) (v.adicCompletion K)
        (Set.range fun i ↦ (b i : L))
      rw [hb, Submodule.baseChange_top, ← Set.range_comp] at h
      exact h.symm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (hspan ▸ Submodule.mem_top : (semilocalEquiv L v).symm z ∈ Submodule.span _ _)
    refine ⟨c, ?_, fun h ↦ absurd h hz⟩
    simp_rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hc
    rw [hc, ← coe_semilocalEquiv]
    exact (semilocalEquiv L v).apply_symm_apply z

/-- **The canonical scalar-extension map of finite adeles is surjective**: every finite adele of
`L` is a sum of finite adeles of `K` times elements of `L`. -/
theorem finiteAdeleBaseChangeHom_surjective :
    Function.Surjective (finiteAdeleBaseChangeHom K L) := by
  classical
  intro y
  choose c hc hci using fun v : HeightOneSpectrum (𝓞 K) ↦
    exists_semilocalHom_sum_tmul_eq K L v fun w ↦ y w.1
  -- The components of `y` above `v` are integral for all but finitely many `v`.
  have hy : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        y w.1 ∈ w.1.adicCompletionIntegers L := by
    have hfin : {w : HeightOneSpectrum (𝓞 L) | y w ∉ w.adicCompletionIntegers L}.Finite :=
      Filter.eventually_cofinite.1 y.2
    refine Filter.eventually_cofinite.2 ((hfin.image (HeightOneSpectrum.under (𝓞 K))).subset ?_)
    intro v hv
    simp only [Set.mem_ofPred_eq, not_forall] at hv
    obtain ⟨⟨w, hw⟩, hwy⟩ := hv
    exact ⟨w, hwy, HeightOneSpectrum.ext hw.over.symm⟩
  -- Assemble the local coefficients into finite adeles of `K`.
  let a (i : Module.Free.ChooseBasisIndex ℤ (𝓞 L)) : FiniteAdeleRing (𝓞 K) K :=
    ⟨fun v ↦ c v i, hy.mono fun v hv ↦ hci v hv i⟩
  refine ⟨∑ i, a i ⊗ₜ[K] (RingOfIntegers.basis L i : L), FiniteAdeleRing.ext L fun w ↦ ?_⟩
  rw [finiteAdeleBaseChangeHom_apply K L _ (w.under (𝓞 K)) ⟨w, inferInstance⟩]
  convert congrFun (hc (w.under (𝓞 K))) ⟨w, inferInstance⟩ using 2
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply]
  -- The component of `a i` at `v` is `c v i` by construction.
  rfl

/-- The canonical scalar-extension map of finite adeles is bijective. -/
theorem finiteAdeleBaseChangeHom_bijective :
    Function.Bijective (finiteAdeleBaseChangeHom K L) :=
  ⟨finiteAdeleBaseChangeHom_injective K L, finiteAdeleBaseChangeHom_surjective K L⟩

/-- Base change of finite adeles is an algebra equivalence over the finite adele ring of the
base field, independently of a topology on the tensor product. -/
def finiteAdeleBaseChangeAlgEquiv :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L ≃ₐ[FiniteAdeleRing (𝓞 K) K] FiniteAdeleRing (𝓞 L) L :=
  AlgEquiv.ofBijective (finiteAdeleBaseChangeHom K L) (finiteAdeleBaseChangeHom_bijective K L)

/-- Forgetting invertibility recovers the canonical base-change homomorphism. -/
@[simp]
theorem finiteAdeleBaseChangeAlgEquiv_toAlgHom :
    (finiteAdeleBaseChangeAlgEquiv K L).toAlgHom = finiteAdeleBaseChangeHom K L :=
  (rfl)

/-- The algebraic inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem finiteAdeleBaseChangeAlgEquiv_symm_algebraMap (x : L) :
    (finiteAdeleBaseChangeAlgEquiv K L).symm
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) = 1 ⊗ₜ[K] x := by
  apply (finiteAdeleBaseChangeAlgEquiv K L).injective
  simp [finiteAdeleBaseChangeAlgEquiv]

variable [TopologicalSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] L)]
  [IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K ⊗[K] L)]

/-- The canonical comparison is continuous for the module topology over the base finite
adele ring. -/
@[continuity, fun_prop]
theorem continuous_finiteAdeleBaseChangeHom : Continuous (finiteAdeleBaseChangeHom K L) := by
  let : ContinuousSMul (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
    continuousSMul_of_algebraMap _ _ (by
      rw [algebraMap_finiteAdeleExtensionAlgebra]
      exact continuous_finiteAdeleExtension (𝓞 K) K (𝓞 L) L)
  exact IsModuleTopology.continuous_of_linearMap (finiteAdeleBaseChangeHom K L).toLinearMap

/-- **Base change of finite adeles** is a continuous algebra equivalence
`𝔸ᶠ_K ⊗[K] L ≃A[𝔸ᶠ_K] 𝔸ᶠ_L` over the finite adele ring of the base field, for the module
topology on the source. -/
def finiteAdeleBaseChangeEquiv :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L ≃A[FiniteAdeleRing (𝓞 K) K] FiniteAdeleRing (𝓞 L) L := by
  let e := finiteAdeleBaseChangeAlgEquiv K L
  have hc : Continuous e := continuous_finiteAdeleBaseChangeHom K L
  -- The tensor product is σ-compact, as a finite free module over a σ-compact ring. The
  -- additive open mapping theorem then gives the inverse.
  letI := IsModuleTopology.isTopologicalAddGroup (FiniteAdeleRing (𝓞 K) K)
    (FiniteAdeleRing (𝓞 K) K ⊗[K] L)
  have : Countable (𝓞 K) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  letI := TauCeti.ModuleTopology.sigmaCompactSpace
    ((Module.finBasis K L).baseChange (FiniteAdeleRing (𝓞 K) K))
  have ho : IsOpenMap e := e.toAddMonoidHom.isOpenMap_of_sigmaCompact e.surjective hc
  exact
    { toAlgEquiv := e
      continuous_toFun := hc
      continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }

/-- Forgetting continuity recovers the algebraic base-change equivalence. -/
@[simp]
theorem finiteAdeleBaseChangeEquiv_toAlgEquiv :
    (finiteAdeleBaseChangeEquiv K L).toAlgEquiv = finiteAdeleBaseChangeAlgEquiv K L :=
  (rfl)

/-- The continuous comparison sends a pure tensor to the extended adele times the diagonal
field element. -/
@[simp]
theorem finiteAdeleBaseChangeEquiv_tmul (a : FiniteAdeleRing (𝓞 K) K) (x : L) :
    finiteAdeleBaseChangeEquiv K L (a ⊗ₜ x) =
      finiteAdeleExtension (𝓞 K) K (𝓞 L) L a * algebraMap L (FiniteAdeleRing (𝓞 L) L) x := by
  have h : (finiteAdeleBaseChangeEquiv K L).toAlgHom = finiteAdeleBaseChangeHom K L := by simp
  exact (AlgHom.congr_fun h (a ⊗ₜ[K] x)).trans (finiteAdeleBaseChangeHom_tmul K L a x)

/-- The inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem finiteAdeleBaseChangeEquiv_symm_algebraMap (x : L) :
    (finiteAdeleBaseChangeEquiv K L).symm
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) = 1 ⊗ₜ[K] x :=
  finiteAdeleBaseChangeAlgEquiv_symm_algebraMap K L x

end TauCeti.GlobalNumberFields
