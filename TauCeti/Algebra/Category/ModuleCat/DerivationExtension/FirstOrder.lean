/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Basic
public import TauCeti.Algebra.Lie.Derivation.BaseChange
public import TauCeti.Algebra.Lie.Derivation.FirstOrder
public import TauCeti.RingTheory.TensorProduct.CentralBaseChange

/-!
# First-order restriction and derivation self-extensions

For an associative `R`-algebra `A`, extend a derivation `δ` to `R[ε] ⊗[R] A`.
Restricting the constant module `R[ε] ⊗[R] M` through `1 + εδ`, and then along
`A → R[ε] ⊗[R] A`, gives exactly `DerivationExtension δ M`. The comparison sends
`s ⊗ m` to `(s.snd • m, s.fst • m)`, so that the submodule is `ε ⊗ M` and the
quotient is reduction modulo `ε`. In particular the sign is positive: this is
restriction through the inverse of `1 - εδ`, not through `1 - εδ` itself.

The comparison is natural in module maps and identifies the entire short exact
sequence, with identity maps at both endpoints. This is an algebraic statement;
it does not assert integration of a derivation or
transport between fixed strict central-character fibers.

The automorphism and its scalar extension are the existing
`derivationLieAlgebra.firstOrderAlgEquiv` and `derivationLieAlgebra.baseChange`.
The constant module uses `CentralBaseChange.module`; coordinates use Mathlib's
`TensorProduct.prodLeft` and `TensorProduct.lid`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups* (2007), for the
  infinitesimal deformation of modules by outer derivations.
-/

public section

open scoped TensorProduct DualNumber
open CategoryTheory

namespace TauCeti.DerivationExtension

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]
  (δ : derivationLieAlgebra R A)

/-- The inclusion of `A` in its dual-number coefficient extension, followed by
`1 + εδ`. Thus restricting through this map uses the inverse of the negative flow. -/
noncomputable def firstOrderRestrictionMap : A →+* DualNumber R ⊗[R] A :=
  (derivationLieAlgebra.firstOrderAlgEquiv (ε : DualNumber R) DualNumber.eps_mul_eps
    (derivationLieAlgebra.baseChange (DualNumber R) δ)).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom

/-- The restriction map has the prescribed positive infinitesimal term. -/
@[simp]
theorem firstOrderRestrictionMap_apply (a : A) :
    firstOrderRestrictionMap δ a =
      (1 : DualNumber R) ⊗ₜ[R] a + ε ⊗ₜ[R] (δ : Module.End R A) a := by
  simp [firstOrderRestrictionMap, TensorProduct.smul_tmul']

variable (M : Type w) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

attribute [local instance low] CentralBaseChange.module

/-- The constant dual-number module restricted through the inverse negative flow.
This uses native `ModuleCat.restrictScalars` on the actual coefficient extension. -/
-- Reducible because its restricted carrier occurs in tensor component formulas.
noncomputable abbrev firstOrderModule : ModuleCat A :=
  (ModuleCat.restrictScalars (firstOrderRestrictionMap δ)).obj
    (ModuleCat.of (DualNumber R ⊗[R] A) (DualNumber R ⊗[R] M))

-- These additive coordinates forget the twisted action. The dual-number carrier is
-- definitionally a product, so the native product-tensor equivalence applies directly.
private noncomputable def firstOrderCoordinates :
    DualNumber R ⊗[R] M ≃+ DerivationExtension δ M :=
  ((TensorProduct.prodLeft R R R R M).trans
    ((TensorProduct.lid R M).prodCongr (TensorProduct.lid R M))).toAddEquiv.trans
      { toFun x := ⟨x.2, x.1⟩
        invFun x := (x.snd, x.fst)
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := by ext <;> simp }

omit [Module A M] [IsScalarTower R A M] in
private theorem firstOrderCoordinates_tmul (s : DualNumber R) (m : M) :
    firstOrderCoordinates δ M (s ⊗ₜ[R] m) = ⟨s.snd • m, s.fst • m⟩ := by
  obtain ⟨r, t⟩ := s
  have h := TensorProduct.prodLeft_tmul R R R R M r t m
  have h' := congrArg
    (fun p : (R ⊗[R] M) × (R ⊗[R] M) =>
      (⟨TensorProduct.lid R M p.2, TensorProduct.lid R M p.1⟩ : DerivationExtension δ M)) h
  exact h'

private theorem firstOrderCoordinates_smul (a : A) (x : DualNumber R ⊗[R] M) :
    firstOrderCoordinates δ M (firstOrderRestrictionMap δ a • x) =
      a • firstOrderCoordinates δ M x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul s m =>
    have h : firstOrderRestrictionMap δ a • (s ⊗ₜ[R] m) =
        s ⊗ₜ[R] (a • m) + (ε * s) ⊗ₜ[R] ((δ : Module.End R A) a • m) := by
      rw [firstOrderRestrictionMap_apply]
      exact (add_smul ((1 : DualNumber R) ⊗ₜ[R] a)
        (ε ⊗ₜ[R] (δ : Module.End R A) a) (s ⊗ₜ[R] m)).trans
          (by simp only [CentralBaseChange.tmul_smul_tmul, one_mul])
    rw [h, map_add, firstOrderCoordinates_tmul, firstOrderCoordinates_tmul,
      firstOrderCoordinates_tmul]
    ext <;> simp only [fst_add, snd_add, fst_smul, snd_smul, DualNumber.snd_mul,
      TrivSqZeroExt.fst_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul,
      one_mul, zero_add, zero_smul, add_zero]
    · exact congrArg₂ (· + ·) (smul_comm (s.snd : R) a m)
        (smul_comm (s.fst : R) ((δ : Module.End R A) a) m)
    · exact smul_comm (s.fst : R) a m

/-- The restricted constant dual-number module is the derivation self-extension.
The coordinates are `(infinitesimal part, constant part)`. -/
noncomputable def firstOrderEquiv : firstOrderModule δ M ≃ₗ[A] DerivationExtension δ M where
  toFun := firstOrderCoordinates δ M
  invFun := (firstOrderCoordinates δ M).symm
  left_inv := (firstOrderCoordinates δ M).left_inv
  right_inv := (firstOrderCoordinates δ M).right_inv
  map_add' := (firstOrderCoordinates δ M).map_add
  map_smul' a x := firstOrderCoordinates_smul δ M a x

/-- The comparison on pure tensors fixes its normalization, including its sign. -/
@[simp]
theorem firstOrderEquiv_tmul (s : DualNumber R) (m : M) :
    firstOrderEquiv δ M (s ⊗ₜ[R] m) = ⟨s.snd • m, s.fst • m⟩ :=
  firstOrderCoordinates_tmul δ M s m

/-- The inverse comparison writes `(u,v)` as `ε ⊗ u + 1 ⊗ v`. -/
@[simp]
theorem firstOrderEquiv_symm_apply (x : DerivationExtension δ M) :
    (firstOrderEquiv δ M).symm x =
      (ε : DualNumber R) ⊗ₜ[R] x.fst + (1 : DualNumber R) ⊗ₜ[R] x.snd := by
  apply (firstOrderCoordinates δ M).injective
  -- Use additive coordinates to avoid the restricted carrier's inherited addition instance.
  calc
    _ = x := (firstOrderCoordinates δ M).apply_symm_apply x
    _ = _ := by ext <;> simp [firstOrderCoordinates_tmul]

/-- The submodule inclusion is precisely multiplication by the dual-number parameter.
This is a named rewrite: the tensor evaluation lemma already gives its simp normal form. -/
theorem firstOrderEquiv_eps_tmul (m : M) :
    firstOrderEquiv δ M ((ε : DualNumber R) ⊗ₜ[R] m) = inlHom δ M m := by
  ext <;> simp

section Sequence

variable (P : Type (max u w)) [AddCommGroup P] [Module A P] [Module R P]
  [IsScalarTower R A P]

/-- The coefficient-restriction extension, with inclusion `m ↦ ε ⊗ m` and
projection given by the constant coefficient. The universe bound puts all three
terms in the same native module category. -/
-- Exposed to retain the actual middle object in the comparison and component formulas.
@[expose] noncomputable def firstOrderShortComplex : ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (X := P) (Y := firstOrderModule δ P)
      ((firstOrderEquiv δ P).symm.toLinearMap ∘ₗ inlHom δ P))
    (ModuleCat.ofHom (X := firstOrderModule δ P)
      (Y := P) (sndHom δ P ∘ₗ (firstOrderEquiv δ P).toLinearMap))
    (by
      ext m
      -- Normalize the native ModuleCat compositions before using the coordinate API.
      change sndHom δ P (firstOrderEquiv δ P
        ((firstOrderEquiv δ P).symm (inlHom δ P m))) = 0
      simp)

/-- The first map of the restriction extension is `ε ⊗ -`. -/
@[simp]
theorem firstOrderShortComplex_f_apply (m : P) :
    (firstOrderShortComplex δ P).f m = (ε : DualNumber R) ⊗ₜ[R] m := by
  -- The native bundled-map projection hides the linear composition from rewriting.
  change (firstOrderEquiv δ P).symm (inlHom δ P m) = _
  apply (firstOrderEquiv δ P).injective
  exact ((firstOrderEquiv δ P).apply_symm_apply _).trans
    (firstOrderEquiv_eps_tmul δ P m).symm

/-- The second map is reduction modulo `ε`, on every pure tensor. -/
@[simp]
theorem firstOrderShortComplex_g_tmul (s : DualNumber R) (m : P) :
    (firstOrderShortComplex δ P).g (s ⊗ₜ[R] m) = s.fst • m := by
  -- The native bundled-map projection hides the linear composition from rewriting.
  change sndHom δ P (firstOrderEquiv δ P (s ⊗ₜ[R] m)) = _
  simp

/-- The coordinate comparison identifies the entire restriction sequence with the
self-extension, using identity comparisons on both endpoints. -/
noncomputable def firstOrderShortComplexIso :
    firstOrderShortComplex δ P ≅ shortComplex δ (ModuleCat.of A P) :=
  ShortComplex.isoMk (Iso.refl _) (firstOrderEquiv δ P).toModuleIso
    (Iso.refl _) (by
      apply ModuleCat.hom_ext
      ext m
      -- Normalize the three native bundled morphisms to their underlying linear maps.
      change inlHom δ P m = firstOrderEquiv δ P
        ((firstOrderEquiv δ P).symm (inlHom δ P m))
      exact ((firstOrderEquiv δ P).apply_symm_apply _).symm)
    (by
      apply ModuleCat.hom_ext
      ext x
      -- Both paths are the same linear composition, through distinct bundled endpoints.
      rfl)

/-- The forward sequence comparison is the identity on the submodule. -/
@[simp]
theorem firstOrderShortComplexIso_hom_τ₁ :
    (firstOrderShortComplexIso δ P).hom.τ₁ = 𝟙 (firstOrderShortComplex δ P).X₁ := (rfl)

/-- The forward middle component is the coordinate comparison. -/
@[simp]
theorem firstOrderShortComplexIso_hom_τ₂ :
    (firstOrderShortComplexIso δ P).hom.τ₂ =
      ModuleCat.ofHom (firstOrderEquiv δ P).toLinearMap := (rfl)

/-- The forward sequence comparison is the identity on the quotient. -/
@[simp]
theorem firstOrderShortComplexIso_hom_τ₃ :
    (firstOrderShortComplexIso δ P).hom.τ₃ = 𝟙 (firstOrderShortComplex δ P).X₃ := (rfl)

/-- The inverse sequence comparison is the identity on the submodule. -/
@[simp]
theorem firstOrderShortComplexIso_inv_τ₁ :
    (firstOrderShortComplexIso δ P).inv.τ₁ = 𝟙 (firstOrderShortComplex δ P).X₁ := (rfl)

/-- The inverse middle component is the inverse coordinate comparison. -/
@[simp]
theorem firstOrderShortComplexIso_inv_τ₂ :
    (firstOrderShortComplexIso δ P).inv.τ₂ =
      ModuleCat.ofHom (firstOrderEquiv δ P).symm.toLinearMap := (rfl)

/-- The inverse sequence comparison is the identity on the quotient. -/
@[simp]
theorem firstOrderShortComplexIso_inv_τ₃ :
    (firstOrderShortComplexIso δ P).inv.τ₃ = 𝟙 (firstOrderShortComplex δ P).X₃ := (rfl)

/-- The native coefficient-restriction sequence is short exact. -/
theorem shortExact_firstOrderShortComplex : (firstOrderShortComplex δ P).ShortExact :=
  ShortComplex.shortExact_of_iso (firstOrderShortComplexIso δ P).symm
    (shortExact_shortComplex δ (ModuleCat.of A P))

end Sequence

variable {M} {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

/-- The comparison is natural for the actual coefficient-extended module map.
No choice of a vector-space splitting is involved. -/
theorem firstOrderEquiv_naturality (f : M →ₗ[A] N) (x : firstOrderModule δ M) :
    firstOrderEquiv δ N (CentralBaseChange.map (DualNumber R) f x) =
      map f (firstOrderEquiv δ M x) := by
  suffices h : firstOrderCoordinates δ N (CentralBaseChange.map (DualNumber R) f x) =
      map f (firstOrderCoordinates δ M x) from h
  -- Restriction changes only the scalar action, not the tensor carrier. Specify that
  -- carrier explicitly so tensor induction sees its constructors through ModuleCat.
  induction (show DualNumber R ⊗[R] M from x) using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
    simp only [CentralBaseChange.map_tmul, firstOrderCoordinates_tmul]
    ext <;> simp

end TauCeti.DerivationExtension
