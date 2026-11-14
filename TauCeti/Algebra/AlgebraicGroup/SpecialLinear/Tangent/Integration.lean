/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BinaryForm.Differential
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.Coalgebra.Comodule.Product
import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.Lie.Sl2.Decomposition

/-!
# Integrating finite-dimensional `sl₂`-modules to rational `SL₂`-representations

Every finite-dimensional representation of `sl (Fin 2) k` over a field `k` of characteristic zero
integrates to a unique rational representation (`Comodule`) of `SL₂`, without assuming that `k` is
algebraically closed or that `M` lives in the universe of `k`.

* **Existence** decomposes `M` as an internal direct sum of irreducible `sl (Fin 2) k`-submodules
  `Nᵢ ≃ V(nᵢ)` (`TauCeti.Sl2Std.exists_isInternal_lieModuleEquiv`), realizes each `V(nᵢ)` as the
  rational `SL₂`-comodule `TauCeti.SpecialLinear.binaryForms k (nᵢ)` via
  `TauCeti.SpecialLinear.binaryFormsEquivSl2Std`, forms the finite product comodule, and transports
  across the direct-sum equivalence.
* **Uniqueness** and **functoriality** follow from representation rigidity
  (`TauCeti.Comodule.ext_of_differential_eq_of_geometricallyConnected` and
  `LinearMap.map_coact_iff_map_differential_of_geometricallyConnected`) together with geometric
  connectedness of `SL₂`
  (`TauCeti.SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`), with
  no finite-dimensionality hypothesis needed on the uniqueness side.

## Main declarations

* `TauCeti.SpecialLinear.existsUnique_comodule_of_lieModule`: every finite-dimensional
  `sl (Fin 2) k`-module over a characteristic-zero field carries a unique `O(SL₂)`-comodule
  structure whose differentiated action agrees with the given Lie-module action across
  `tangentLieEquivSl 2`.
* `TauCeti.SpecialLinear.comoduleOfLieModule`: that canonical `O(SL₂)`-comodule structure,
  characterized by `differential_comoduleOfLieModule` and `eq_comoduleOfLieModule_iff`.
* `TauCeti.SpecialLinear.comoduleHomOfLieModuleHom`: every `sl (Fin 2) k`-module homomorphism
  between integrated modules is a morphism of `O(SL₂)`-comodules.
* `TauCeti.SpecialLinear.exists_subcomodule_comoduleOfLieModule_iff`: a `k`-submodule underlies an
  `O(SL₂)`-subcomodule if and only if it is `sl (Fin 2) k`-stable.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.2.
* J. S. Milne, *Algebraic Groups* (2017), §12 and §22.
-/

public section

open LieAlgebra
open scoped DirectSum TensorProduct

namespace TauCeti.SpecialLinear

universe u w w'

section Aux

private def finZeroEquivPUnit (R : Type*) [CommSemiring R] (B : Fin 0 → Type*)
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)] :
    PUnit.{1} ≃ₗ[R] (∀ i : Fin 0, B i) where
  toFun _ i := Fin.elim0 i
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv _ := funext fun i ↦ Fin.elim0 i
  map_add' _ _ := funext fun i ↦ Fin.elim0 i
  map_smul' _ _ := funext fun i ↦ Fin.elim0 i

private def finSuccEquivProd (R : Type*) [CommSemiring R] {r : ℕ} (B : Fin (r + 1) → Type*)
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)] :
    (B 0 × (∀ i : Fin r, B i.succ)) ≃ₗ[R] (∀ i : Fin (r + 1), B i) where
  toFun p := Fin.cases p.1 p.2
  invFun f := (f 0, fun i ↦ f i.succ)
  left_inv _ := by simp
  right_inv _ := funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
  map_add' _ _ := funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
  map_smul' _ _ := funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i

@[implicit_reducible]
private noncomputable def finPiComodule {R H : Type*} [CommRing R] [CommRing H] [Bialgebra R H] :
    ∀ (r : ℕ) (B : Fin r → Type*) [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
      (_ : ∀ i, Comodule R H (B i)), Comodule R H (∀ i, B i)
  | 0, B, _, _, _ =>
    Comodule.Transport (R := R) (C := H) (finZeroEquivPUnit R B)
  | r + 1, B, _, _, c =>
    letI : Comodule R H (B 0) := c 0
    letI : Comodule R H (∀ i : Fin r, B i.succ) :=
      finPiComodule r (fun i ↦ B i.succ) (fun i ↦ c i.succ)
    letI : Comodule R H (B 0 × (∀ i : Fin r, B i.succ)) := Comodule.Prod
    Comodule.Transport (R := R) (C := H) (finSuccEquivProd R B)

private theorem differential_finPiComodule {R H : Type*} [CommRing R] [CommRing H]
    [Bialgebra R H] :
    ∀ (r : ℕ) (B : Fin r → Type*) [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
      (c : ∀ i, Comodule R H (B i))
      (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (f : ∀ i, B i) (i : Fin r),
      (@Comodule.differential R H (∀ j, B j) _ _ _ _ _ (finPiComodule r B c) d f) i =
        @Comodule.differential R H (B i) _ _ _ _ _ (c i) d (f i)
  | 0, _, _, _, _, _, _, i => Fin.elim0 i
  | r + 1, B, _, _, c, d, f, i => by
    let _ : Comodule R H (B 0) := c 0
    let _ : Comodule R H (∀ j : Fin r, B j.succ) :=
      finPiComodule r (fun j ↦ B j.succ) (fun j ↦ c j.succ)
    let _ : Comodule R H (B 0 × (∀ j : Fin r, B j.succ)) := Comodule.Prod
    rw [finPiComodule, Comodule.differential_transport (finSuccEquivProd R B),
      Comodule.differential_prod]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [finSuccEquivProd]
    · simp only [finSuccEquivProd, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
        LinearEquiv.coe_symm_mk, Fin.cases_succ]
      exact differential_finPiComodule r (fun j ↦ B j.succ) (fun j ↦ c j.succ) d
        (fun j ↦ f j.succ) j

@[reducible]
private noncomputable def finiteTypeSL2 (k : Type u) [Field k] : FiniteTypeCommHopfAlgCat k :=
  ⟨coordinateHopfAlgebra k 2, by
    rw [← finiteTypeCoordinateHopfAlgebra_obj]
    exact (finiteTypeCoordinateHopfAlgebra k 2).property⟩

end Aux

section Integration

attribute [local instance] polynomialComodule

/-- **Existence and uniqueness of rational `SL₂`-integration.** Every finite-dimensional
`sl (Fin 2) k`-module over a field `k` of characteristic zero carries a unique `O(SL₂)`-comodule
structure whose differentiated action agrees with the Lie-module action across
`tangentLieEquivSl 2`. -/
theorem existsUnique_comodule_of_lieModule (k : Type u) [Field k] [CharZero k]
    (M : Type w) [AddCommGroup M] [Module k M] [Module.Finite k M]
    [LieRingModule (SpecialLinear.sl (Fin 2) k) M]
    [LieModule k (SpecialLinear.sl (Fin 2) k) M] :
    ∃! c : Comodule k (coordinateHopfAlgebra k 2) M,
      ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
          (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M),
        @Comodule.differential k (coordinateHopfAlgebra k 2) M _ _ _ _ _ c d m =
          ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ := by
  obtain ⟨r, N, n, hint, hequiv⟩ := Sl2Std.exists_isInternal_lieModuleEquiv k M
  let φ (i : Fin r) : N i ≃ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ Sl2Std k (n i) := (hequiv i).some
  let eSummand (i : Fin r) : binaryForms k (n i) ≃ₗ[k] (N i).toSubmodule :=
    (binaryFormsEquivSl2Std k (n i)).trans (φ i).symm.toLinearEquiv
  let eSum : (∀ i : Fin r, (N i).toSubmodule) ≃ₗ[k] M :=
    (DirectSum.linearEquivFunOnFintype k (Fin r) (fun i ↦ (N i).toSubmodule)).symm.trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i ↦ (N i).toSubmodule) hint)
  have heSum (g : ∀ i, (N i).toSubmodule) : eSum g = ∑ i, (g i : M) := by
    conv_lhs => rw [← Finset.univ_sum_single g]
    simp only [eSum, map_sum, LinearEquiv.trans_apply,
      DirectSum.linearEquivFunOnFintype_symm_single]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact DirectSum.coeLinearMap_of (fun j ↦ (N j).toSubmodule) i (g i)
  let E : (∀ i : Fin r, binaryForms k (n i)) ≃ₗ[k] M :=
    (LinearEquiv.piCongrRight eSummand).trans eSum
  let _ : Comodule k (coordinateHopfAlgebra k 2) (∀ i : Fin r, binaryForms k (n i)) :=
    finPiComodule r (fun i ↦ binaryForms k (n i)) (fun _ ↦ inferInstance)
  let cM : Comodule k (coordinateHopfAlgebra k 2) M :=
    Comodule.Transport (R := k) (C := coordinateHopfAlgebra k 2) E
  have hcM (d : Derivation k (coordinateHopfAlgebra k 2)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M) :
      @Comodule.differential k (coordinateHopfAlgebra k 2) M _ _ _ _ _ cM d m =
        ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ := by
    rw [Comodule.differential_transport E]
    set g := E.symm m
    have hm : m = E g := (E.apply_symm_apply m).symm
    conv_rhs => rw [hm]
    simp only [E, LinearEquiv.trans_apply, heSum, LinearEquiv.piCongrRight_apply, lie_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [eSummand, LinearEquiv.trans_apply, LieModuleEquiv.coe_toLinearEquiv]
    rw [differential_finPiComodule, binaryFormsEquivSl2Std_differential]
    exact congrArg Subtype.val ((φ i).symm.toLieModuleHom.map_lie _ _)
  refine ⟨cM, hcM, fun c' hc' ↦ ?_⟩
  exact Comodule.ext_of_differential_eq_of_geometricallyConnected
    (H := finiteTypeSL2 k)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)
    fun d m ↦ (hc' d m).trans (hcM d m).symm

/-- **The canonical `O(SL₂)`-comodule integrating a finite-dimensional `sl (Fin 2) k`-module**
over a field `k` of characteristic zero. -/
@[implicit_reducible]
noncomputable def comoduleOfLieModule (k : Type u) [Field k] [CharZero k]
    (M : Type w) [AddCommGroup M] [Module k M] [Module.Finite k M]
    [LieRingModule (SpecialLinear.sl (Fin 2) k) M]
    [LieModule k (SpecialLinear.sl (Fin 2) k) M] :
    Comodule k (coordinateHopfAlgebra k 2) M :=
  (existsUnique_comodule_of_lieModule k M).choose

section API

variable {k : Type u} [Field k] [CharZero k]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module.Finite k M]
  [LieRingModule (SpecialLinear.sl (Fin 2) k) M]
  [LieModule k (SpecialLinear.sl (Fin 2) k) M]
variable {N : Type w'} [AddCommGroup N] [Module k N] [Module.Finite k N]
  [LieRingModule (SpecialLinear.sl (Fin 2) k) N]
  [LieModule k (SpecialLinear.sl (Fin 2) k) N]

/-- The differentiated action of `comoduleOfLieModule` is the given `sl (Fin 2) k`-action across
`tangentLieEquivSl 2`. -/
theorem differential_comoduleOfLieModule
    (d : Derivation k (coordinateHopfAlgebra k 2)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M) :
    letI := comoduleOfLieModule k M
    Comodule.differential (R := k) (H := coordinateHopfAlgebra k 2) d m =
      ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ :=
  (existsUnique_comodule_of_lieModule k M).choose_spec.1 d m

/-- Evaluating `Comodule.differential` for `comoduleOfLieModule` at `(tangentLieEquivSl 2).symm A`
recovers `⁅A, m⁆`. -/
theorem differential_comoduleOfLieModule_symm
    (A : SpecialLinear.sl (Fin 2) k) (m : M) :
    letI := comoduleOfLieModule k M
    Comodule.differential (R := k) (H := coordinateHopfAlgebra k 2)
        ((tangentLieEquivSl (R := k) (B := k) 2).symm A) m = ⁅A, m⁆ := by
  let _ := comoduleOfLieModule k M
  rw [differential_comoduleOfLieModule, LieEquiv.apply_symm_apply]

/-- An `O(SL₂)`-comodule structure on `M` equals `comoduleOfLieModule k M` if and only if its
differential agrees with the `sl (Fin 2) k`-action across `tangentLieEquivSl 2`. -/
theorem eq_comoduleOfLieModule_iff (c : Comodule k (coordinateHopfAlgebra k 2) M) :
    c = comoduleOfLieModule k M ↔
      ∀ (d : Derivation k (coordinateHopfAlgebra k 2)
          (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k 2) k)) (m : M),
        @Comodule.differential k (coordinateHopfAlgebra k 2) M _ _ _ _ _ c d m =
          ⁅tangentLieEquivSl (R := k) (B := k) 2 d, m⁆ :=
  ⟨fun h ↦ h ▸ differential_comoduleOfLieModule,
    (existsUnique_comodule_of_lieModule k M).choose_spec.2 c⟩

/-- **Functoriality of `SL₂`-integration.** Every `sl (Fin 2) k`-module homomorphism between
finite-dimensional `sl (Fin 2) k`-modules is a morphism of `O(SL₂)`-comodules for
`comoduleOfLieModule`. -/
noncomputable def comoduleHomOfLieModuleHom
    (f : M →ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ N) :
    letI := comoduleOfLieModule k M
    letI := comoduleOfLieModule k N
    Comodule.Hom k (coordinateHopfAlgebra k 2) M N :=
  letI := comoduleOfLieModule k M
  letI := comoduleOfLieModule k N
  { toLinearMap := f.toLinearMap
    map_coact :=
      (f.toLinearMap.map_coact_iff_map_differential_of_geometricallyConnected
        (H := finiteTypeSL2 k)
        (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)).mpr fun d m ↦ by
          rw [differential_comoduleOfLieModule, differential_comoduleOfLieModule]
          exact f.map_lie (tangentLieEquivSl (R := k) (B := k) 2 d) m }

@[simp]
theorem comoduleHomOfLieModuleHom_toLinearMap
    (f : M →ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ N) :
    letI := comoduleOfLieModule k M
    letI := comoduleOfLieModule k N
    (comoduleHomOfLieModuleHom f).toLinearMap = f.toLinearMap :=
  (rfl)

@[simp]
theorem comoduleHomOfLieModuleHom_apply
    (f : M →ₗ⁅k,SpecialLinear.sl (Fin 2) k⁆ N) (m : M) :
    letI := comoduleOfLieModule k M
    letI := comoduleOfLieModule k N
    comoduleHomOfLieModuleHom f m = f m :=
  (rfl)

/-- A `k`-submodule of `M` underlies an `O(SL₂)`-subcomodule for `comoduleOfLieModule k M` if and
only if it is `sl (Fin 2) k`-stable. -/
theorem exists_subcomodule_comoduleOfLieModule_iff (S : Submodule k M) :
    letI := comoduleOfLieModule k M
    (∃ W : Subcomodule k (coordinateHopfAlgebra k 2) M, W.toSubmodule = S) ↔
      ∀ (A : SpecialLinear.sl (Fin 2) k), ∀ m ∈ S, ⁅A, m⁆ ∈ S := by
  let _ := comoduleOfLieModule k M
  rw [S.exists_subcomodule_iff_forall_differential_mem_of_geometricallyConnected
    (H := finiteTypeSL2 k)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)]
  constructor
  · intro h A m hm
    have h' := h ((tangentLieEquivSl (R := k) (B := k) 2).symm A) m hm
    rwa [differential_comoduleOfLieModule_symm] at h'
  · intro h d m hm
    rw [differential_comoduleOfLieModule]
    exact h (tangentLieEquivSl (R := k) (B := k) 2 d) m hm

end API

end Integration

end TauCeti.SpecialLinear
