/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.RingTheory.DedekindDomain.Different.Basic
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.NormTrace.Pi

/-!
# Trace duals and the different ideal across a semilocal decomposition

Let `R` be a domain (integrally closed when fractional ideals or the different ideal are formed)
with fraction field `K`, let `L / K` be a finite separable extension, and let `S` be a finite
projective integral closure of `R` in `L`. Suppose `R'` is an integrally closed domain with
fraction field `K'` over `K`, and `(S' i, L' i)` is a finite family of completed or localized
extensions equipped with semilocal algebra isomorphisms

`eField : K' ⊗[K] L ≃ₐ[K'] ∀ i, L' i` and `eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i`

compatible with ring homomorphisms `fField i : L →+* L' i` and `fInt i : S →+* S' i`.

This file extracts the abstract semilocal comparison shared by Dedekind-domain adic completions
(`TauCeti/RingTheory/DedekindDomain/Different/Completion.lean`) and function-field place
completions (`TauCeti/FieldTheory/FunctionField/Different/Completion.lean`), combining the
trace-dual expansion transfer `AlgEquiv.sum_trace_mul_smul_eq` (`TauCeti.RingTheory.NormTrace.Pi`)
with the single-ring comparison lemmas `RingHom.span_traceDual_one_eq_traceDual_one_of_forall`
(`TauCeti.RingTheory.DedekindDomain.Different.DualFamily`),
`RingHom.extended_dual_one_eq_dual_one_of_span_eq`, and
`RingHom.map_differentIdeal_eq_differentIdeal_of_extended_eq`
(`TauCeti.RingTheory.DedekindDomain.Different.Basic`):

* `AlgEquiv.mem_traceDual_one_of_semilocal`: every element of the global trace dual `Sᵛ` maps into
  the local trace dual `(S' i)ᵛ`.
* `AlgEquiv.span_traceDual_one_eq_traceDual_one_of_semilocal`: the local trace dual `(S' i)ᵛ` is
  spanned over `S' i` by the image of `Sᵛ`.
* `AlgEquiv.extended_dual_one_eq_dual_one_of_semilocal`: the fractional-ideal trace dual commutes
  with extension along `fInt i`.
* `AlgEquiv.map_differentIdeal_eq_differentIdeal_of_semilocal`: the different ideal
  `differentIdeal R S` extends along `fInt i` to `differentIdeal R' (S' i)`.
* `AlgEquiv.map_differentIdeal_semilocal`: extending `differentIdeal R S` to `R' ⊗[R] S` and
  transporting along `eInt` gives the product ideal `Ideal.pi fun i ↦ differentIdeal R' (S' i)`.
-/

public section

open IsDedekindDomain Module
open scoped TensorProduct nonZeroDivisors

namespace AlgEquiv

section Semilocal

variable {ι : Type*} [Finite ι]
variable {R K S L R' K' : Type*}
  [CommRing R] [Field K] [CommRing S] [Field L]
  [CommRing R'] [Field K']
  [Algebra R K] [Algebra K L] [Algebra R S] [Algebra S L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [Algebra R R'] [Algebra R' K'] [Algebra K K'] [Algebra R K']
  [IsScalarTower R R' K'] [IsScalarTower R K K']
variable {S' : ι → Type*} {L' : ι → Type*}
  [∀ i, CommRing (S' i)] [∀ i, Field (L' i)]
  [∀ i, Algebra K' (L' i)] [∀ i, FiniteDimensional K' (L' i)]
  [∀ i, Algebra R' (S' i)] [∀ i, Algebra (S' i) (L' i)] [∀ i, Algebra R' (L' i)]
  [∀ i, IsScalarTower R' K' (L' i)] [∀ i, IsScalarTower R' (S' i) (L' i)]

/-- Under compatible field and integral semilocal decompositions `(eField, eInt)`, every element of
the global trace dual `Submodule.traceDual R K 1` maps into `Submodule.traceDual R' K' 1` in each
component `i`. -/
theorem mem_traceDual_one_of_semilocal
    (eField : K' ⊗[K] L ≃ₐ[K'] ∀ i, L' i) (eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i)
    (fField : ∀ i, L →+* L' i) (fInt : ∀ i, S →+* S' i)
    (heField : ∀ (a : K') (x : L) (i : ι),
      eField (a ⊗ₜ[K] x) i = algebraMap K' (L' i) a * fField i x)
    (heInt : ∀ (a : R') (x : S) (i : ι),
      eInt (a ⊗ₜ[R] x) i = algebraMap R' (S' i) a * fInt i x)
    (hfCompat : ∀ (i : ι) (x : S),
      algebraMap (S' i) (L' i) (fInt i x) = fField i (algebraMap S L x))
    (i : ι) ⦃d : L⦄ (hd : d ∈ Submodule.traceDual R K (1 : Submodule S L)) :
    fField i d ∈ Submodule.traceDual R' K' (1 : Submodule (S' i) (L' i)) := by
  classical
  -- Construct the canonical `R`-algebra map `R' ⊗[R] S →ₐ[R] K' ⊗[K] L` internally so callers do
  -- not need to supply its compatibility proof separately.
  let toField : R' ⊗[R] S →ₐ[R] K' ⊗[K] L :=
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : K' →ₐ[K] K' ⊗[K] L).restrictScalars R |>.comp
        (IsScalarTower.toAlgHom R R' K'))
      ((Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).restrictScalars R |>.comp
        (IsScalarTower.toAlgHom R S L))
      fun _ _ ↦ .all _ _
  have htoField_tmul (a : R') (x : S) :
      toField (a ⊗ₜ[R] x) = algebraMap R' K' a ⊗ₜ[K] algebraMap S L x := by
    simp [toField]
  have hcompat (t : R' ⊗[R] S) :
      eField (toField t) = fun j ↦ algebraMap (S' j) (L' j) (eInt t j) := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
      funext j
      simp [congrFun hx j, congrFun hy j]
    | tmul a x =>
      funext j
      rw [htoField_tmul, heField, heInt, map_mul, hfCompat,
        ← IsScalarTower.algebraMap_apply R' K' (L' j),
        IsScalarTower.algebraMap_apply R' (S' j) (L' j)]
  have hmem (t : R' ⊗[R] S) :
      Algebra.trace K' (K' ⊗[K] L) (toField t * (1 ⊗ₜ[K] d)) ∈ (algebraMap R' K').range := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu =>
      rw [map_add, add_mul, map_add]
      exact add_mem ht hu
    | tmul a x =>
      obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
      refine ⟨a * algebraMap R R' r, ?_⟩
      rw [TauCeti.Algebra.trace_map_tmul_mul toField htoField_tmul, mul_comm (algebraMap S L x),
        ← Algebra.traceForm_apply, ← hr, map_mul,
        ← IsScalarTower.algebraMap_apply R R' K', IsScalarTower.algebraMap_apply R K K']
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  -- Lift `z`, placed in the `i`-th component of `∀ j, S' j`, to `R' ⊗[R] S` via `eInt`.
  obtain ⟨t, ht⟩ := eInt.surjective (Pi.single i z)
  have hξ : toField t = eField.symm (Pi.single i (algebraMap (S' i) (L' i) z)) := by
    rw [AlgEquiv.eq_symm_apply, hcompat, ht]
    funext j
    obtain rfl | hj := eq_or_ne j i
    · simp
    · simp [Pi.single_eq_of_ne hj]
  have htr := eField.trace_symm_single_mul i (algebraMap (S' i) (L' i) z) ((1 : K') ⊗ₜ[K] d)
  rw [heField, map_one, one_mul] at htr
  rw [Algebra.traceForm_apply, mul_comm, ← htr, ← hξ]
  exact hmem t

/-- **The local trace dual is spanned by the global one** in a semilocal decomposition. -/
theorem span_traceDual_one_eq_traceDual_one_of_semilocal
    [IsDomain R] [IsFractionRing R K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure S R L] [Module.Finite R S] [Module.Projective R S]
    (eField : K' ⊗[K] L ≃ₐ[K'] ∀ i, L' i) (eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i)
    (fField : ∀ i, L →+* L' i) (fInt : ∀ i, S →+* S' i)
    (heField : ∀ (a : K') (x : L) (i : ι),
      eField (a ⊗ₜ[K] x) i = algebraMap K' (L' i) a * fField i x)
    (heInt : ∀ (a : R') (x : S) (i : ι),
      eInt (a ⊗ₜ[R] x) i = algebraMap R' (S' i) a * fInt i x)
    (hfCompat : ∀ (i : ι) (x : S),
      algebraMap (S' i) (L' i) (fInt i x) = fField i (algebraMap S L x))
    (i : ι) :
    Submodule.span (S' i) (fField i '' Submodule.traceDual R K (1 : Submodule S L)) =
      Submodule.traceDual R' K' (1 : Submodule (S' i) (L' i)) :=
  (fField i).span_traceDual_one_eq_traceDual_one_of_forall (fInt i) (hfCompat i)
    (eField.mem_traceDual_one_of_semilocal eInt fField fInt heField heInt hfCompat i)
    (fun b y hb z ↦ by
      simpa [heField] using eField.sum_trace_mul_smul_eq b y hb i z)

/-- **Fractional-ideal trace duals commute with completion** in a semilocal decomposition. -/
theorem extended_dual_one_eq_dual_one_of_semilocal
    [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K]
    [IsDomain S] [IsFractionRing S L] [IsIntegralClosure S R L]
    [Module.Finite R S] [Module.Projective R S]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDomain R'] [IsIntegrallyClosed R'] [IsFractionRing R' K']
    (eField : K' ⊗[K] L ≃ₐ[K'] ∀ i, L' i) (eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i)
    (fField : ∀ i, L →+* L' i) (fInt : ∀ i, S →+* S' i)
    (heField : ∀ (a : K') (x : L) (i : ι),
      eField (a ⊗ₜ[K] x) i = algebraMap K' (L' i) a * fField i x)
    (heInt : ∀ (a : R') (x : S) (i : ι),
      eInt (a ⊗ₜ[R] x) i = algebraMap R' (S' i) a * fInt i x)
    (hfCompat : ∀ (i : ι) (x : S),
      algebraMap (S' i) (L' i) (fInt i x) = fField i (algebraMap S L x))
    (i : ι) [IsDomain (S' i)] [IsFractionRing (S' i) (L' i)]
    [IsIntegralClosure (S' i) R' (L' i)]
    [Algebra.IsSeparable K' (L' i)] (hfInj : Function.Injective (fInt i)) :
    (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)).extended (L' i)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hfInj) =
      FractionalIdeal.dual R' K' (1 : FractionalIdeal (S' i)⁰ (L' i)) :=
  (fField i).extended_dual_one_eq_dual_one_of_span_eq (fInt i) hfInj (hfCompat i)
    (eField.span_traceDual_one_eq_traceDual_one_of_semilocal eInt fField fInt heField heInt
      hfCompat i)

/-- **The different ideal commutes with completion** in a semilocal decomposition. -/
theorem map_differentIdeal_eq_differentIdeal_of_semilocal
    [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K]
    [IsDedekindDomain S] [IsFractionRing S L] [IsIntegralClosure S R L]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDomain R'] [IsIntegrallyClosed R'] [IsFractionRing R' K']
    (eField : K' ⊗[K] L ≃ₐ[K'] ∀ i, L' i) (eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i)
    (fField : ∀ i, L →+* L' i) (fInt : ∀ i, S →+* S' i)
    (heField : ∀ (a : K') (x : L) (i : ι),
      eField (a ⊗ₜ[K] x) i = algebraMap K' (L' i) a * fField i x)
    (heInt : ∀ (a : R') (x : S) (i : ι),
      eInt (a ⊗ₜ[R] x) i = algebraMap R' (S' i) a * fInt i x)
    (hfCompat : ∀ (i : ι) (x : S),
      algebraMap (S' i) (L' i) (fInt i x) = fField i (algebraMap S L x))
    (i : ι) [IsDedekindDomain (S' i)] [IsFractionRing (S' i) (L' i)]
    [IsIntegralClosure (S' i) R' (L' i)] [Module.IsTorsionFree R' (S' i)]
    [Algebra.IsSeparable K' (L' i)] (hfInj : Function.Injective (fInt i)) :
    (differentIdeal R S).map (fInt i) = differentIdeal R' (S' i) :=
  (fInt i).map_differentIdeal_eq_differentIdeal_of_extended_eq (K := K) (L := L)
    (K' := K') (L₀ := L' i) hfInj
    (eField.extended_dual_one_eq_dual_one_of_semilocal eInt fField fInt heField heInt hfCompat i
      hfInj)

end Semilocal

section SemilocalIdeal

variable {ι R S R' : Type*} [Finite ι]
  [CommRing R] [IsDomain R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.IsTorsionFree R S]
  [CommRing R'] [IsDomain R'] [Algebra R R']
  {S' : ι → Type*} [∀ i, CommRing (S' i)] [∀ i, IsDedekindDomain (S' i)]
  [∀ i, Algebra R' (S' i)] [∀ i, Module.IsTorsionFree R' (S' i)]

/-- **The different ideal across an integral semilocal decomposition.** Extending
`differentIdeal R S` to `R' ⊗[R] S` and transporting along `eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i`
produces the product of the local different ideals `Ideal.pi fun i ↦ differentIdeal R' (S' i)`. -/
theorem map_differentIdeal_semilocal
    (eInt : R' ⊗[R] S ≃ₐ[R'] ∀ i, S' i) (fInt : ∀ i, S →+* S' i)
    (heInt : ∀ (a : R') (x : S) (i : ι),
      eInt (a ⊗ₜ[R] x) i = algebraMap R' (S' i) a * fInt i x)
    (hLocal : ∀ i : ι, (differentIdeal R S).map (fInt i) = differentIdeal R' (S' i)) :
    ((differentIdeal R S).map
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S)).map eInt =
      Ideal.pi fun i ↦ differentIdeal R' (S' i) := by
  let f : S →+* ∀ i, S' i :=
    eInt.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom
  have hmap : ((differentIdeal R S).map
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S)).map eInt =
      (differentIdeal R S).map f :=
    Ideal.map_map (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom
      eInt.toRingEquiv.toRingHom
  have hproj (i : ι) :
      ((differentIdeal R S).map f).map (Pi.evalRingHom S' i) = differentIdeal R' (S' i) := by
    rw [Ideal.map_map, ← hLocal i]
    congr 1
    ext x
    simpa [f] using heInt 1 x i
  have hJ : (differentIdeal R S).map f = Ideal.pi (Ideal.piOrderIso ((differentIdeal R S).map f)) :=
    SetLike.coe_injective <| by
      conv_lhs => rw [← Ideal.piOrderIso.symm_apply_apply ((differentIdeal R S).map f)]
      exact (Ideal.coe_piOrderIso_symm_apply _).trans (Set.ext fun _ ↦ by simp [Ideal.mem_pi])
  rw [hmap, hJ]
  refine congrArg Ideal.pi (funext fun i ↦ ?_)
  rw [← Ideal.map_evalRingHom_pi (I := Ideal.piOrderIso ((differentIdeal R S).map f)) i, ← hJ,
    hproj i]

end SemilocalIdeal

end AlgEquiv

end
