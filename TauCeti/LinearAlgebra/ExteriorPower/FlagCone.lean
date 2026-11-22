/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.ExteriorPower.Decomposable
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
import TauCeti.LinearAlgebra.TensorProduct.Segre
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# The affine cone of exterior flag vectors

For an `R`-module `M` and a natural number `d`, the exterior flag space
`FlagSpace R M d = (((⋀⁰ M ⊗ ⋀¹ M) ⊗ ⋀² M) ⊗ ⋯ ⊗ ⋀ᵈ M)` carries the flag vector
`exteriorFlagVector R d v = 1 ⊗ v₀ ⊗ (v₀ ∧ v₁) ⊗ ⋯ ⊗ (v₀ ∧ ⋯ ∧ v_{d-1})` associated to a tuple
`v : Fin d → M`. Scalar multiples of such flag vectors form `exteriorFlagCone R M d`, the affine
cone over the Plücker--Segre image of the variety of `d`-step flags in `M`.

Over a field `k` with `M` finite-dimensional (in arbitrary characteristic, including `char k = 2`),
we prove that `exteriorFlagCone k M d` is cut out inside `FlagSpace k M d` by the set
`exteriorFlagForms k M d` of degree-`2` homogeneous polynomials in `(FlagSpace k M d)*` that vanish
on `exteriorFlagCone k M d`:
* `2 × 2` Segre minors force pure-tensor factorizations across each tensor product;
* quadratic Plücker contraction relations (`Decomposable.lean`) force each exterior factor to be
  decomposable;
* squares of linear contraction-incidence forms force each prefix span to lie in the next.

When `d = dim_k M`, every nonzero vector in `exteriorFlagCone k M d` is a unit multiple of the flag
vector of a basis `b` of `M`, and every linear automorphism stabilizing the line spanned by that
flag vector has upper-triangular matrix in `b`.

## Main definitions

* `TauCeti.exteriorPower.FlagSpace`: iterated tensor product `⋀⁰ M ⊗ ⋀¹ M ⊗ ⋯ ⊗ ⋀ᵈ M`.
* `TauCeti.exteriorPower.exteriorFlagVector`: the flag tensor built from prefix exterior products
  of `v : Fin d → M`.
* `TauCeti.exteriorPower.exteriorFlagMap`: functorial action of linear maps on `FlagSpace`.
* `TauCeti.exteriorPower.exteriorFlagCone`: scalar multiples of `exteriorFlagVector`.
* `TauCeti.exteriorPower.exteriorFlagForms`: degree-`2` homogeneous forms vanishing on
  `exteriorFlagCone`.

## Main results

* `TauCeti.exteriorPower.mem_exteriorFlagCone_iff`: over a field, a vector in `FlagSpace k M d`
  lies in `exteriorFlagCone k M d` if and only if every form in `exteriorFlagForms k M d` vanishes
  at it.
* `TauCeti.exteriorPower.exists_basis_of_mem_exteriorFlagCone_of_finrank_eq`: in top degree
  `d = finrank k M`, every nonzero element of `exteriorFlagCone k M d` comes from a basis of `M`.
* `TauCeti.exteriorPower.isUpperTriangular_toMatrix_of_exteriorFlagMap_mem_span`: a linear
  automorphism preserving the line spanned by `exteriorFlagVector k d b` is upper triangular in `b`.

## References

* W. Fulton, *Young Tableaux*, LMSST 35, Cambridge University Press (1997), §9.1 (equations of flag
  varieties via Plücker and incidence relations).
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, Springer (1975), §21.3.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Theorem 17.9(a), p. 354.
-/

public section

open scoped TensorProduct

namespace TauCeti.exteriorPower

universe u v w

section FlagSpace

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- Auxiliary bundle carrying `FlagSpace R M d` together with its `R`-module instances. -/
private def flagSpaceAux : ℕ → Σ (V : Type (max u v)), Σ (_ : AddCommGroup V), Module R V
  | 0 => ⟨⋀[R]^0 M, inferInstance, inferInstance⟩
  | r + 1 =>
      let _ : AddCommGroup (flagSpaceAux r).1 := (flagSpaceAux r).2.1
      let _ : Module R (flagSpaceAux r).1 := (flagSpaceAux r).2.2
      ⟨(flagSpaceAux r).1 ⊗[R] ⋀[R]^(r + 1) M, inferInstance, inferInstance⟩

/-- The iterated exterior-power tensor space `⋀⁰ M ⊗ ⋀¹ M ⊗ ⋯ ⊗ ⋀ᵈ M` hosting the Plücker--Segre
embedding of `d`-step flags in `M`. -/
def FlagSpace (d : ℕ) : Type (max u v) :=
  (flagSpaceAux R M d).1

/-- Additive commutative group structure on `FlagSpace R M d`. -/
@[no_expose] noncomputable instance instAddCommGroupFlagSpace (d : ℕ) :
    AddCommGroup (FlagSpace R M d) :=
  (flagSpaceAux R M d).2.1

/-- `R`-module structure on `FlagSpace R M d`. -/
@[no_expose] noncomputable instance instModuleFlagSpace (d : ℕ) : Module R (FlagSpace R M d) :=
  (flagSpaceAux R M d).2.2

/-- Canonical linear equivalence `FlagSpace R M 0 ≃ₗ[R] ⋀[R]^0 M`. -/
noncomputable def flagSpaceZeroEquiv : FlagSpace R M 0 ≃ₗ[R] ⋀[R]^0 M :=
  LinearEquiv.refl R (⋀[R]^0 M)

/-- Canonical linear equivalence
`FlagSpace R M (r + 1) ≃ₗ[R] FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M`. -/
noncomputable def flagSpaceSuccEquiv (r : ℕ) :
    FlagSpace R M (r + 1) ≃ₗ[R] FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M :=
  LinearEquiv.refl R (FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M)

/-- When `M` is finitely generated over `R`, every `FlagSpace R M d` is finitely generated. -/
instance instFiniteFlagSpace [Module.Finite R M] : (d : ℕ) → Module.Finite R (FlagSpace R M d)
  | 0 => Module.Finite.equiv (flagSpaceZeroEquiv R M).symm
  | r + 1 => by
      have : Module.Finite R (FlagSpace R M r) := instFiniteFlagSpace r
      exact Module.Finite.equiv (flagSpaceSuccEquiv R M r).symm

variable {M}

/-- The exterior flag vector `1 ⊗ v₀ ⊗ (v₀ ∧ v₁) ⊗ ⋯ ⊗ (v₀ ∧ ⋯ ∧ v_{d-1})` associated to a family
`v : Fin d → M`. -/
noncomputable def exteriorFlagVector : (d : ℕ) → (Fin d → M) → FlagSpace R M d
  | 0, v => (flagSpaceZeroEquiv R M).symm (_root_.exteriorPower.ιMulti R 0 v)
  | r + 1, v =>
      (flagSpaceSuccEquiv R M r).symm
        (exteriorFlagVector r (v ∘ Fin.castSucc) ⊗ₜ[R] _root_.exteriorPower.ιMulti R (r + 1) v)

variable {R}

/-- Base-case unfolding of `exteriorFlagVector` in degree `0`. -/
theorem exteriorFlagVector_zero (v : Fin 0 → M) :
    exteriorFlagVector R 0 v =
      (flagSpaceZeroEquiv R M).symm (_root_.exteriorPower.ιMulti R 0 v) := by
  simp [exteriorFlagVector]

/-- Recursive unfolding of `exteriorFlagVector` in degree `r + 1`. -/
theorem exteriorFlagVector_succ (r : ℕ) (v : Fin (r + 1) → M) :
    exteriorFlagVector R (r + 1) v =
      (flagSpaceSuccEquiv R M r).symm
        (exteriorFlagVector R r (v ∘ Fin.castSucc) ⊗ₜ[R]
          _root_.exteriorPower.ιMulti R (r + 1) v) := by
  simp [exteriorFlagVector]

/-- Image of `exteriorFlagVector R 0 v` under `flagSpaceZeroEquiv`. -/
@[simp]
theorem flagSpaceZeroEquiv_exteriorFlagVector (v : Fin 0 → M) :
    flagSpaceZeroEquiv R M (exteriorFlagVector R 0 v) = _root_.exteriorPower.ιMulti R 0 v := by
  rw [exteriorFlagVector_zero, LinearEquiv.apply_symm_apply]

/-- Image of `exteriorFlagVector R (r + 1) v` under `flagSpaceSuccEquiv`. -/
@[simp]
theorem flagSpaceSuccEquiv_exteriorFlagVector (r : ℕ) (v : Fin (r + 1) → M) :
    flagSpaceSuccEquiv R M r (exteriorFlagVector R (r + 1) v) =
      exteriorFlagVector R r (v ∘ Fin.castSucc) ⊗ₜ[R] _root_.exteriorPower.ιMulti R (r + 1) v := by
  rw [exteriorFlagVector_succ, LinearEquiv.apply_symm_apply]

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Functorial action of an `R`-linear map `M →ₗ[R] N` on `FlagSpace`. -/
noncomputable def exteriorFlagMap : (d : ℕ) → (M →ₗ[R] N) → FlagSpace R M d →ₗ[R] FlagSpace R N d
  | 0, f =>
      (flagSpaceZeroEquiv R N).symm.toLinearMap ∘ₗ
        _root_.exteriorPower.map 0 f ∘ₗ (flagSpaceZeroEquiv R M).toLinearMap
  | r + 1, f =>
      (flagSpaceSuccEquiv R N r).symm.toLinearMap ∘ₗ
        TensorProduct.map (exteriorFlagMap r f) (_root_.exteriorPower.map (r + 1) f) ∘ₗ
          (flagSpaceSuccEquiv R M r).toLinearMap

/-- Base-case unfolding of `exteriorFlagMap` in degree `0`. -/
theorem exteriorFlagMap_zero (f : M →ₗ[R] N) :
    exteriorFlagMap 0 f =
      (flagSpaceZeroEquiv R N).symm.toLinearMap ∘ₗ
        _root_.exteriorPower.map 0 f ∘ₗ (flagSpaceZeroEquiv R M).toLinearMap := by
  simp [exteriorFlagMap]

/-- Recursive unfolding of `exteriorFlagMap` in degree `r + 1`. -/
theorem exteriorFlagMap_succ (r : ℕ) (f : M →ₗ[R] N) :
    exteriorFlagMap (r + 1) f =
      (flagSpaceSuccEquiv R N r).symm.toLinearMap ∘ₗ
        TensorProduct.map (exteriorFlagMap r f) (_root_.exteriorPower.map (r + 1) f) ∘ₗ
          (flagSpaceSuccEquiv R M r).toLinearMap := by
  simp [exteriorFlagMap]

/-- Evaluation of `exteriorFlagMap 0 f` under `flagSpaceZeroEquiv`. -/
@[simp]
theorem flagSpaceZeroEquiv_exteriorFlagMap_apply (f : M →ₗ[R] N) (w : FlagSpace R M 0) :
    flagSpaceZeroEquiv R N (exteriorFlagMap 0 f w) =
      _root_.exteriorPower.map 0 f (flagSpaceZeroEquiv R M w) := by
  simp [exteriorFlagMap_zero]

/-- Evaluation of `exteriorFlagMap (r + 1) f` under `flagSpaceSuccEquiv`. -/
@[simp]
theorem flagSpaceSuccEquiv_exteriorFlagMap_apply (r : ℕ) (f : M →ₗ[R] N)
    (w : FlagSpace R M (r + 1)) :
    flagSpaceSuccEquiv R N r (exteriorFlagMap (r + 1) f w) =
      TensorProduct.map (exteriorFlagMap r f) (_root_.exteriorPower.map (r + 1) f)
        (flagSpaceSuccEquiv R M r w) := by
  simp [exteriorFlagMap_succ]

/-- `exteriorFlagMap d` sends the identity linear map to the identity. -/
@[simp]
theorem exteriorFlagMap_id (d : ℕ) :
    exteriorFlagMap d (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  induction d with
  | zero => exact LinearMap.ext fun w ↦ (flagSpaceZeroEquiv R M).injective (by simp)
  | succ r ih => exact LinearMap.ext fun w ↦ (flagSpaceSuccEquiv R M r).injective (by simp [ih])

/-- `exteriorFlagMap d` preserves composition of linear maps. -/
theorem exteriorFlagMap_comp {P : Type*} [AddCommGroup P] [Module R P] (d : ℕ)
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    exteriorFlagMap d (g ∘ₗ f) = exteriorFlagMap d g ∘ₗ exteriorFlagMap d f := by
  induction d with
  | zero =>
    exact LinearMap.ext fun w ↦
      (flagSpaceZeroEquiv R P).injective (by simp [_root_.exteriorPower.map_comp])
  | succ r ih =>
    exact LinearMap.ext fun w ↦
      (flagSpaceSuccEquiv R P r).injective
        (by simp [ih, _root_.exteriorPower.map_comp, TensorProduct.map_map])

/-- `exteriorFlagMap` carries the flag vector of `v` to the flag vector of `f ∘ v`. -/
@[simp]
theorem exteriorFlagMap_exteriorFlagVector (d : ℕ) (f : M →ₗ[R] N) (v : Fin d → M) :
    exteriorFlagMap d f (exteriorFlagVector R d v) = exteriorFlagVector R d (f ∘ v) := by
  induction d with
  | zero => exact (flagSpaceZeroEquiv R N).injective (by simp)
  | succ r ih => exact (flagSpaceSuccEquiv R N r).injective (by simp [ih, Function.comp_assoc])

/-- Over a field, `exteriorFlagVector k d v` is nonzero if and only if `v` is linearly
independent. -/
@[simp]
theorem exteriorFlagVector_ne_zero_iff {k : Type u} {V : Type v} [Field k]
    [AddCommGroup V] [Module k V] {d : ℕ} {v : Fin d → V} :
    exteriorFlagVector k d v ≠ 0 ↔ LinearIndependent k v := by
  induction d with
  | zero =>
    rw [← (flagSpaceZeroEquiv k V).map_ne_zero_iff, flagSpaceZeroEquiv_exteriorFlagVector]
    exact _root_.exteriorPower.ιMulti_ne_zero_iff v
  | succ r ih =>
    rw [← (flagSpaceSuccEquiv k V r).map_ne_zero_iff, flagSpaceSuccEquiv_exteriorFlagVector]
    refine ⟨fun h ↦ ?_, fun hv ↦ ?_⟩
    · rw [← _root_.exteriorPower.ιMulti_ne_zero_iff v]
      exact fun h0 ↦ h (by rw [h0, TensorProduct.tmul_zero])
    · exact TauCeti.tmul_ne_zero (R := k)
        (ih.mpr (hv.comp Fin.castSucc (Fin.castSucc_injective r)))
        ((_root_.exteriorPower.ιMulti_ne_zero_iff v).mpr hv)

end FlagSpace

section ConeDefinitions

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The affine cone of exterior flag vectors in `FlagSpace R M d`: all scalar multiples of
`exteriorFlagVector R d v` as `v` ranges over `Fin d → M`. -/
def exteriorFlagCone (d : ℕ) : Set (FlagSpace R M d) :=
  {w | ∃ (c : R) (v : Fin d → M), w = c • exteriorFlagVector R d v}

/-- The set of degree-`2` homogeneous polynomials in `SymmetricAlgebra R (Dual R (FlagSpace R M d))`
that vanish identically on `exteriorFlagCone R M d`. -/
def exteriorFlagForms (d : ℕ) :
    Set (_root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R M d))) :=
  {s | s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R (FlagSpace R M d)) 2 ∧
    ∀ w ∈ exteriorFlagCone R M d,
      _root_.SymmetricAlgebra.lift (Module.Dual.eval R (FlagSpace R M d) w) s = 0}

variable {R M}

/-- Zero belongs to `exteriorFlagCone R M d`. -/
theorem zero_mem_exteriorFlagCone (d : ℕ) : (0 : FlagSpace R M d) ∈ exteriorFlagCone R M d :=
  ⟨0, 0, by simp⟩

/-- Every exterior flag vector belongs to `exteriorFlagCone R M d`. -/
theorem exteriorFlagVector_mem_exteriorFlagCone {d : ℕ} (v : Fin d → M) :
    exteriorFlagVector R d v ∈ exteriorFlagCone R M d :=
  ⟨1, v, by simp⟩

/-- The cone `exteriorFlagCone R M d` is closed under scalar multiplication. -/
theorem smul_mem_exteriorFlagCone {d : ℕ} (c : R) {w : FlagSpace R M d}
    (hw : w ∈ exteriorFlagCone R M d) : c • w ∈ exteriorFlagCone R M d := by
  obtain ⟨a, v, rfl⟩ := hw
  exact ⟨c * a, v, (mul_smul c a _).symm⟩

/-- Induced flag maps carry `exteriorFlagCone R M d` into `exteriorFlagCone R N d`. -/
theorem exteriorFlagMap_mem_exteriorFlagCone {N : Type w} [AddCommGroup N] [Module R N]
    {d : ℕ} (f : M →ₗ[R] N) {w : FlagSpace R M d} (hw : w ∈ exteriorFlagCone R M d) :
    exteriorFlagMap d f w ∈ exteriorFlagCone R N d := by
  obtain ⟨c, v, rfl⟩ := hw
  exact ⟨c, f ∘ v, by rw [map_smul, exteriorFlagMap_exteriorFlagVector]⟩

/-- Every form in `exteriorFlagForms R M d` is homogeneous of degree `2`. -/
theorem mem_homogeneousSubmodule_of_mem_exteriorFlagForms {d : ℕ}
    {s : _root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R M d))}
    (hs : s ∈ exteriorFlagForms R M d) :
    s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R (FlagSpace R M d)) 2 :=
  hs.1

/-- If a linear map `p` sends `exteriorFlagCone` into `exteriorFlagCone`, pulling back along
`p.dualMap` sends `exteriorFlagForms` into `exteriorFlagForms`. -/
theorem map_dualMap_mem_exteriorFlagForms {N : Type w} [AddCommGroup N] [Module R N]
    {d₁ d₂ : ℕ} {p : FlagSpace R M d₁ →ₗ[R] FlagSpace R N d₂}
    (hp : ∀ w ∈ exteriorFlagCone R M d₁, p w ∈ exteriorFlagCone R N d₂)
    {s : _root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R N d₂))}
    (hs : s ∈ exteriorFlagForms R N d₂) :
    _root_.SymmetricAlgebra.map R p.dualMap s ∈ exteriorFlagForms R M d₁ :=
  ⟨TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule p.dualMap hs.1, fun w hw ↦ by
    rw [_root_.SymmetricAlgebra.lift_eval_map_dualMap]
    exact hs.2 (p w) (hp w hw)⟩

end ConeDefinitions

section QuadraticCriterion

variable {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]

private noncomputable def quadFormOfTensor (V : Type*) [AddCommGroup V] [Module k V] :
    Module.Dual k V ⊗[k] Module.Dual k V →ₗ[k]
      TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k V) 2 :=
  TensorProduct.lift (DirectSum.gMulLHom k fun n ↦
      TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k V) n) ∘ₗ
    TensorProduct.map
      (TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv k (Module.Dual k V)).symm.toLinearMap
      (TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv k (Module.Dual k V)).symm.toLinearMap

private noncomputable def bilinearToQuadForm {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (B : V →ₗ[k] V →ₗ[k] k) :
    TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k V) 2 :=
  quadFormOfTensor V ((TensorProduct.dualDistribEquiv k V V).symm (TensorProduct.lift B))

private theorem lift_eval_bilinearToQuadForm {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (B : V →ₗ[k] V →ₗ[k] k) (v : V) :
    _root_.SymmetricAlgebra.lift (Module.Dual.eval k V v) (bilinearToQuadForm B : _) = B v v := by
  have hcomp : (_root_.SymmetricAlgebra.lift (Module.Dual.eval k V v)).toLinearMap ∘ₗ
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k V) 2).subtype ∘ₗ
        quadFormOfTensor (k := k) V =
      Module.Dual.eval k (V ⊗[k] V) (v ⊗ₜ[k] v) ∘ₗ TensorProduct.dualDistrib k V V :=
    TensorProduct.ext' fun _ _ ↦ by
      simp [quadFormOfTensor, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
        TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleOneEquiv_symm_apply]
  simpa [bilinearToQuadForm, ← TensorProduct.toLinearMap_dualDistribEquiv] using
    LinearMap.congr_fun hcomp ((TensorProduct.dualDistribEquiv k V V).symm (TensorProduct.lift B))

private theorem exists_tmul_of_forall_exteriorFlagForms {r : ℕ} {w : FlagSpace k M (r + 1)}
    (hw : ∀ s ∈ exteriorFlagForms k M (r + 1),
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M (r + 1)) w) s = 0) :
    ∃ (w_r : FlagSpace k M r) (θ : ⋀[k]^(r + 1) M),
      w = (flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ) := by
  suffices ∃ (w_r : FlagSpace k M r) (θ : ⋀[k]^(r + 1) M),
      flagSpaceSuccEquiv k M r w = w_r ⊗ₜ[k] θ by
    obtain ⟨w_r, θ, h⟩ := this
    exact ⟨w_r, θ, (flagSpaceSuccEquiv k M r).eq_symm_apply.mpr h⟩
  refine (TensorProduct.exists_eq_tmul_iff _).mpr fun φ₁ φ₂ ψ₁ ψ₂ ↦ ?_
  let δ := (flagSpaceSuccEquiv k M r).toLinearMap.dualMap ∘ₗ
    TensorProduct.dualDistrib k (FlagSpace k M r) (⋀[k]^(r + 1) M)
  let ι := _root_.SymmetricAlgebra.ι k (Module.Dual k (FlagSpace k M (r + 1)))
  let s := ι (δ (φ₁ ⊗ₜ ψ₁)) * ι (δ (φ₂ ⊗ₜ ψ₂)) - ι (δ (φ₁ ⊗ₜ ψ₂)) * ι (δ (φ₂ ⊗ₜ ψ₁))
  have hs : s ∈ exteriorFlagForms k M (r + 1) :=
    ⟨Submodule.sub_mem _
        (SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _)
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _))
        (SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _)
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _)), by
      rintro _ ⟨c, v, rfl⟩
      simp [s, ι, δ]
      ring⟩
  simpa [s, ι, δ, sub_eq_zero] using hw s hs

section FiniteDimensional

variable [FiniteDimensional k M]

private theorem decomposable_of_forall_exteriorFlagForms {r : ℕ}
    {w_r : FlagSpace k M r} {θ : ⋀[k]^(r + 1) M} (hw_r : w_r ≠ 0)
    (hw : ∀ s ∈ exteriorFlagForms k M (r + 1),
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M (r + 1))
        ((flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ))) s = 0) :
    θ ∈ Set.range (_root_.exteriorPower.ιMulti k (r + 1)) := by
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one k hw_r
  let p₂ : FlagSpace k M (r + 1) →ₗ[k] ⋀[k]^(r + 1) M :=
    (TensorProduct.lid k (⋀[k]^(r + 1) M)).toLinearMap ∘ₗ
      TensorProduct.map φ₀ LinearMap.id ∘ₗ (flagSpaceSuccEquiv k M r).toLinearMap
  have hp₂ : p₂ ((flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ)) = θ := by
    simp [p₂, hφ₀]
  refine (_root_.exteriorPower.mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero θ).mpr
    fun η ↦ (Module.forall_dual_apply_eq_zero_iff k _).mp fun ξ ↦ ?_
  let B : ⋀[k]^(r + 1) M →ₗ[k] ⋀[k]^(r + 1) M →ₗ[k] k :=
    LinearMap.mk₂ k
      (fun θ₁ θ₂ ↦ ξ (_root_.ExteriorAlgebra.ι k
        (_root_.exteriorPower.contract k M r η θ₁) * (θ₂ : ExteriorAlgebra k M)))
      (fun _ _ _ ↦ by simp [add_mul]) (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp [mul_add]) (fun _ _ _ ↦ by simp)
  let s := _root_.SymmetricAlgebra.map k p₂.dualMap (bilinearToQuadForm B : _)
  have hs : s ∈ exteriorFlagForms k M (r + 1) :=
    ⟨TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _ (bilinearToQuadForm B).property, by
      rintro _ ⟨c, v, rfl⟩
      rw [_root_.SymmetricAlgebra.lift_eval_map_dualMap, lift_eval_bilinearToQuadForm]
      have hpv : p₂ (c • exteriorFlagVector k (r + 1) v) =
          (c * φ₀ (exteriorFlagVector k r (v ∘ Fin.castSucc))) •
            _root_.exteriorPower.ιMulti k (r + 1) v := by
        simp [p₂, mul_smul]
      simp only [hpv, map_smul, LinearMap.smul_apply, B, LinearMap.mk₂_apply,
        _root_.exteriorPower.ιMulti_apply_coe, _root_.exteriorPower.ι_contract_mul_ιMulti_eq_zero,
        map_zero, smul_zero]⟩
  have hval := hw s hs
  rwa [_root_.SymmetricAlgebra.lift_eval_map_dualMap, hp₂, lift_eval_bilinearToQuadForm] at hval

private noncomputable def incidenceDual {m : ℕ}
    (η : ⋀[k]^m (Module.Dual k M)) (φ : Module.Dual k (FlagSpace k M m))
    (ξ : Module.Dual k (ExteriorAlgebra k M)) :
    Module.Dual k (FlagSpace k M (m + 2)) :=
  let g₁ : FlagSpace k M (m + 1) →ₗ[k] M :=
    _root_.exteriorPower.contract k M m η ∘ₗ
      (TensorProduct.lid k (⋀[k]^(m + 1) M)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ (flagSpaceSuccEquiv k M m).toLinearMap
  TensorProduct.lift (LinearMap.mk₂ k
    (fun (a : FlagSpace k M (m + 1)) (β : ⋀[k]^(m + 2) M) ↦
      ξ (_root_.ExteriorAlgebra.ι k (g₁ a) * (β : ExteriorAlgebra k M)))
    (fun _ _ _ ↦ by simp [add_mul]) (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp [mul_add]) (fun _ _ _ ↦ by simp)) ∘ₗ
      (flagSpaceSuccEquiv k M (m + 1)).toLinearMap

private theorem incidenceDual_exteriorFlagVector_eq_zero {m : ℕ}
    (η : ⋀[k]^m (Module.Dual k M)) (φ : Module.Dual k (FlagSpace k M m))
    (ξ : Module.Dual k (ExteriorAlgebra k M)) (v : Fin (m + 2) → M) :
    incidenceDual η φ ξ (exteriorFlagVector k (m + 2) v) = 0 := by
  have hmem : _root_.exteriorPower.contract k M m η
      (_root_.exteriorPower.ιMulti k (m + 1) (v ∘ Fin.castSucc)) ∈
      Submodule.span k (Set.range v) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _)
      (_root_.exteriorPower.contract_ιMulti_mem_span η (v ∘ Fin.castSucc))
  simp only [incidenceDual, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    flagSpaceSuccEquiv_exteriorFlagVector (r := m + 1), flagSpaceSuccEquiv_exteriorFlagVector,
    TensorProduct.lift.tmul, LinearMap.mk₂_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lid_tmul, map_smul, smul_mul_assoc]
  rw [_root_.exteriorPower.ι_mul_ιMulti_eq_zero_of_mem_span hmem, map_zero, smul_zero]

private theorem span_le_of_forall_exteriorFlagForms {r : ℕ} {c₀ : k} {u : Fin r → M}
    {v₀ : Fin (r + 1) → M} (hc₀ : c₀ ≠ 0) (hu : LinearIndependent k u)
    (hv₀ : LinearIndependent k v₀)
    (hw : ∀ s ∈ exteriorFlagForms k M (r + 1),
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M (r + 1))
        ((flagSpaceSuccEquiv k M r).symm
          ((c₀ • exteriorFlagVector k r u) ⊗ₜ[k] _root_.exteriorPower.ιMulti k (r + 1) v₀)))
        s = 0) :
    Submodule.span k (Set.range u) ≤ Submodule.span k (Set.range v₀) := by
  cases r with
  | zero => simp [Set.range_eq_empty]
  | succ m =>
    rw [← _root_.exteriorPower.range_contract_flip_ιMulti hu]
    rintro _ ⟨η, rfl⟩
    refine (mem_span_range_iff_ι_mul_ιMulti_eq_zero hv₀ _).mpr
      ((Module.forall_dual_apply_eq_zero_iff k _).mp fun ξ ↦ ?_)
    let y_m : FlagSpace k M m := exteriorFlagVector k m (u ∘ Fin.castSucc)
    have hy_m : y_m ≠ 0 :=
      exteriorFlagVector_ne_zero_iff.mpr (hu.comp _ (Fin.castSucc_injective m))
    obtain ⟨φ_m, hφ_m⟩ := Module.Projective.exists_dual_eq_one k hy_m
    let L := incidenceDual η φ_m ξ
    let s := _root_.SymmetricAlgebra.ι k _ L * _root_.SymmetricAlgebra.ι k _ L
    have hs : s ∈ exteriorFlagForms k M (m + 2) :=
      ⟨SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ L)
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ L), by
        rintro _ ⟨c, v, rfl⟩
        simp only [s, map_mul, _root_.SymmetricAlgebra.lift_ι_apply, map_smul,
          LinearMap.smul_apply, Module.Dual.eval_apply]
        rw [show L (exteriorFlagVector k (m + 2) v) = 0 from
            incidenceDual_exteriorFlagVector_eq_zero η φ_m ξ v, smul_zero, mul_zero]⟩
    have hLw : L ((flagSpaceSuccEquiv k M (m + 1)).symm
        ((c₀ • exteriorFlagVector k (m + 1) u) ⊗ₜ[k]
          _root_.exteriorPower.ιMulti k (m + 2) v₀)) = 0 :=
      mul_self_eq_zero.mp (by simpa [s] using hw s hs)
    rw [LinearMap.flip_apply]
    simpa [L, incidenceDual, y_m, hφ_m, hc₀] using hLw

private theorem mem_exteriorFlagCone_succ_of_span_le {r : ℕ} {c₀ : k} {u : Fin r → M}
    {v₀ : Fin (r + 1) → M} (hu : LinearIndependent k u) (hv₀ : LinearIndependent k v₀)
    (hle : Submodule.span k (Set.range u) ≤ Submodule.span k (Set.range v₀)) :
    (flagSpaceSuccEquiv k M r).symm
        ((c₀ • exteriorFlagVector k r u) ⊗ₜ[k] _root_.exteriorPower.ιMulti k (r + 1) v₀) ∈
      exteriorFlagCone k M (r + 1) := by
  have hnot_le : ¬ Submodule.span k (Set.range v₀) ≤ Submodule.span k (Set.range u) := fun hge ↦ by
    have hdim := Submodule.finrank_mono hge
    rw [finrank_span_eq_card hv₀, finrank_span_eq_card hu, Fintype.card_fin,
      Fintype.card_fin] at hdim
    omega
  rw [Submodule.span_le, Set.subset_def] at hnot_le
  push Not at hnot_le
  obtain ⟨_, ⟨j, rfl⟩, hv₀j⟩ := hnot_le
  let v : Fin (r + 1) → M := Fin.snoc u (v₀ j)
  have hv : LinearIndependent k v := linearIndependent_finSnoc.mpr ⟨hu, hv₀j⟩
  have hv_le : Submodule.span k (Set.range v) ≤ Submodule.span k (Set.range v₀) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact i.lastCases
      (by simpa [v] using (Submodule.subset_span ⟨j, rfl⟩ : v₀ j ∈ Submodule.span k (Set.range v₀)))
      fun i₀ ↦ by simpa [v] using hle (Submodule.subset_span ⟨i₀, rfl⟩)
  have hv_span : Submodule.span k (Set.range v) = Submodule.span k (Set.range v₀) :=
    Submodule.eq_of_le_of_finrank_eq hv_le
      (by rw [finrank_span_eq_card hv, finrank_span_eq_card hv₀])
  obtain ⟨c₁, hc₁⟩ := _root_.exteriorPower.exists_units_smul_ιMulti_of_span_eq hv₀ hv hv_span.symm
  refine ⟨c₀ * c₁, v, (flagSpaceSuccEquiv k M r).injective ?_⟩
  have hcast : v ∘ Fin.castSucc = u := funext fun x ↦ by simp [v]
  simp [hc₁, Units.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
    mul_comm, hcast]

/-- **Quadratic equations of the exterior flag cone.** Over a field `k` of arbitrary characteristic,
a vector in `FlagSpace k M d` for a finite-dimensional `k`-vector space `M` lies in
`exteriorFlagCone k M d` if and only if every quadratic form in `exteriorFlagForms k M d` vanishes
at it. -/
theorem mem_exteriorFlagCone_iff {d : ℕ} (w : FlagSpace k M d) :
    w ∈ exteriorFlagCone k M d ↔
      ∀ s ∈ exteriorFlagForms k M d,
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M d) w) s = 0 := by
  refine ⟨fun hw s hs ↦ hs.2 w hw, fun hw ↦ ?_⟩
  induction d with
  | zero =>
    refine ⟨_root_.exteriorPower.zeroEquiv k M (flagSpaceZeroEquiv k M w), Fin.elim0,
      ((flagSpaceZeroEquiv k M).trans (_root_.exteriorPower.zeroEquiv k M)).injective (by simp)⟩
  | succ r ih =>
    by_cases hw0 : w = 0
    · exact hw0 ▸ zero_mem_exteriorFlagCone (r + 1)
    obtain ⟨w_r, θ, rfl⟩ := exists_tmul_of_forall_exteriorFlagForms hw
    have hw_r0 : w_r ≠ 0 := fun h ↦ hw0 (by simp [h])
    have hθ0 : θ ≠ 0 := fun h ↦ hw0 (by simp [h])
    obtain ⟨ψ₀, hψ₀⟩ := Module.Projective.exists_dual_eq_one k hθ0
    let p₁ : FlagSpace k M (r + 1) →ₗ[k] FlagSpace k M r :=
      (TensorProduct.rid k (FlagSpace k M r)).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id ψ₀ ∘ₗ (flagSpaceSuccEquiv k M r).toLinearMap
    have hp₁_cone : ∀ z ∈ exteriorFlagCone k M (r + 1), p₁ z ∈ exteriorFlagCone k M r := by
      rintro _ ⟨c, v, rfl⟩
      exact ⟨c * ψ₀ (_root_.exteriorPower.ιMulti k (r + 1) v), v ∘ Fin.castSucc,
        by simp [p₁, mul_smul]⟩
    have hw_r_cone : w_r ∈ exteriorFlagCone k M r := ih w_r fun s₀ hs₀ ↦ by
      have hval := hw _ (map_dualMap_mem_exteriorFlagForms hp₁_cone hs₀)
      have hp₁w : p₁ ((flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ)) = w_r := by
        simp [p₁, hψ₀]
      rwa [_root_.SymmetricAlgebra.lift_eval_map_dualMap, hp₁w] at hval
    obtain ⟨c₀, u, rfl⟩ := hw_r_cone
    have hc₀ : c₀ ≠ 0 := fun h ↦ hw_r0 (by simp [h])
    have hu : LinearIndependent k u :=
      exteriorFlagVector_ne_zero_iff.mp fun h ↦ hw_r0 (by simp [h])
    obtain ⟨v₀, hv₀_eq⟩ := decomposable_of_forall_exteriorFlagForms hw_r0 hw
    subst hv₀_eq
    have hv₀ : LinearIndependent k v₀ :=
      (_root_.exteriorPower.ιMulti_ne_zero_iff (K := k) v₀).mp hθ0
    exact mem_exteriorFlagCone_succ_of_span_le hu hv₀
      (span_le_of_forall_exteriorFlagForms hc₀ hu hv₀ hw)

end FiniteDimensional

end QuadraticCriterion

section CompleteFlag

variable {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]

private theorem mem_span_prefix_of_exteriorFlagVector_eq_smul {d : ℕ} {u v : Fin d → M} {c : k}
    (hv : LinearIndependent k v) (hc : c ≠ 0)
    (h : exteriorFlagVector k d u = c • exteriorFlagVector k d v) (j : Fin d) :
    u j ∈ Submodule.span k (Set.range (v ∘ Fin.castLE j.isLt)) := by
  induction d generalizing c with
  | zero => exact j.elim0
  | succ r ih =>
    have h' :
        exteriorFlagVector k r (u ∘ Fin.castSucc) ⊗ₜ[k] _root_.exteriorPower.ιMulti k (r + 1) u =
          (c • exteriorFlagVector k r (v ∘ Fin.castSucc)) ⊗ₜ[k]
            _root_.exteriorPower.ιMulti k (r + 1) v := by
      simpa [TensorProduct.smul_tmul'] using congrArg (flagSpaceSuccEquiv k M r) h
    have hne : (c • exteriorFlagVector k r (v ∘ Fin.castSucc)) ⊗ₜ[k]
        _root_.exteriorPower.ιMulti k (r + 1) v ≠ 0 := by
      rw [← TensorProduct.smul_tmul', ← flagSpaceSuccEquiv_exteriorFlagVector, ← map_smul,
        LinearEquiv.map_ne_zero_iff]
      exact smul_ne_zero hc (exteriorFlagVector_ne_zero_iff.mpr hv)
    obtain ⟨a, ha₁, ha₂⟩ := TensorProduct.exists_units_smul_of_tmul_eq_tmul h'.symm hne
    refine j.lastCases ?_ fun i ↦ ?_
    · have hspan := (_root_.exteriorPower.span_range_eq_of_ιMulti_eq_smul hv a.ne_zero
        (by rw [ha₂, Units.smul_def])).2
      have hrange : Set.range (v ∘ Fin.castLE (Fin.last r).isLt) = Set.range v :=
        Set.ext fun x ↦ by simp
      rw [hrange, ← hspan]
      exact Submodule.subset_span ⟨Fin.last r, rfl⟩
    · have ha_smul : exteriorFlagVector k r (u ∘ Fin.castSucc) =
          (a⁻¹.val * c) • exteriorFlagVector k r (v ∘ Fin.castSucc) := by
        rw [mul_smul, ← Units.smul_def, ha₁, inv_smul_smul]
      have hi := ih (hv.comp Fin.castSucc (Fin.castSucc_injective r))
        (mul_ne_zero a⁻¹.ne_zero hc) ha_smul i
      have hcomp : (v ∘ Fin.castSucc) ∘ Fin.castLE i.isLt =
          v ∘ Fin.castLE i.castSucc.isLt := rfl
      rwa [hcomp] at hi

/-- A linear automorphism `f : M ≃ₗ[k] M` whose induced map on `FlagSpace k M d` preserves the
line spanned by `exteriorFlagVector k d b` has upper-triangular matrix in `b`. -/
theorem isUpperTriangular_toMatrix_of_exteriorFlagMap_mem_span {d : ℕ}
    (b : Module.Basis (Fin d) k M) (f : M ≃ₗ[k] M)
    (hf : exteriorFlagMap d f.toLinearMap (exteriorFlagVector k d b) ∈
      k ∙ exteriorFlagVector k d b) :
    (LinearMap.toMatrix b b f.toLinearMap).IsUpperTriangular := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  rw [exteriorFlagMap_exteriorFlagVector] at hc
  have hfb : LinearIndependent k (f.toLinearMap ∘ b) :=
    b.linearIndependent.map' f.toLinearMap f.ker
  have hc0 : c ≠ 0 :=
    fun h0 ↦ (exteriorFlagVector_ne_zero_iff.mpr hfb) (by rw [← hc, h0, zero_smul])
  intro i j hji
  rw [LinearMap.toMatrix_apply]
  have hmem := mem_span_prefix_of_exteriorFlagVector_eq_smul b.linearIndependent hc0 hc.symm j
  have hle : Submodule.span k (Set.range (b ∘ Fin.castLE j.isLt)) ≤ LinearMap.ker (b.coord i) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    have hti : Fin.castLE j.isLt t ≠ i :=
      fun heq ↦ (lt_of_le_of_lt t.is_le hji).ne (congrArg Fin.val heq)
    simp [Module.Basis.coord_apply, hti]
  exact hle hmem

/-- When `Module.finrank k M = d`, every nonzero vector in `exteriorFlagCone k M d` is a unit
multiple of the flag vector of a basis `b : Basis (Fin d) k M`. -/
theorem exists_basis_of_mem_exteriorFlagCone_of_finrank_eq [FiniteDimensional k M] {d : ℕ}
    (hd : Module.finrank k M = d) {w : FlagSpace k M d} (hw : w ∈ exteriorFlagCone k M d)
    (hw0 : w ≠ 0) :
    ∃ (c : kˣ) (b : Module.Basis (Fin d) k M), w = c • exteriorFlagVector k d b := by
  obtain ⟨c, v, rfl⟩ := hw
  have hc : c ≠ 0 := fun h ↦ hw0 (by simp [h])
  have hv : LinearIndependent k v :=
    exteriorFlagVector_ne_zero_iff.mp fun h ↦ hw0 (by simp [h])
  let b : Module.Basis (Fin d) k M :=
    basisOfLinearIndependentOfCardEqFinrank' v hv ((Fintype.card_fin d).trans hd.symm)
  exact ⟨Units.mk0 c hc, b, by
    simp [b, Units.smul_def, coe_basisOfLinearIndependentOfCardEqFinrank']⟩

end CompleteFlag

end TauCeti.exteriorPower
