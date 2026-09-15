/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.FunLike.Graded
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs

/-!
# Morphisms of differential graded right modules

A morphism of differential graded right modules is an `Aᵐᵒᵖ`-linear map which preserves every
homogeneous degree and commutes with the differentials.  This file bundles these maps and supplies
their extensionality, identity, and composition API.  They form the degree-zero closed maps which
later enter the morphism complexes and DG category of right modules.

## Main definitions

* `TauCeti.DGRightModuleHom`: a degree-zero right-module map commuting with the differentials.
* `TauCeti.DGRightModuleHom.id` and `TauCeti.DGRightModuleHom.comp`: identity and composition.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
-/

public section

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {ℳN : ℤ → Submodule R N}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] {dN : N →ₗ[R] N}
  {ℳP : ℤ → Submodule R P}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
    [DirectSum.Decomposition ℳP] {dP : P →ₗ[R] P}

/-- A morphism of differential graded right modules: a right-module homomorphism which preserves
the internal degree and commutes with the differentials. -/
structure DGRightModuleHom (hM : IsDGRightModule h ℳ dM) (hN : IsDGRightModule h ℳN dN)
    extends M →ₗ[Aᵐᵒᵖ] N where
  /-- A DG right-module morphism preserves each homogeneous degree. -/
  map_mem' : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → toLinearMap x ∈ ℳN q
  /-- A DG right-module morphism commutes with the differentials. -/
  map_d' (x : M) : dN (toLinearMap x) = toLinearMap (dM x)

namespace DGRightModuleHom

variable {hM : IsDGRightModule h ℳ dM} {hN : IsDGRightModule h ℳN dN}
  {hP : IsDGRightModule h ℳP dP}

/-- Two DG right-module morphisms are equal if their underlying module homomorphisms are equal. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : DGRightModuleHom hM hN → M →ₗ[Aᵐᵒᵖ] N) := by
  rintro ⟨f, hf, hdf⟩ ⟨g, hg, hdg⟩ hfg
  cases hfg
  rfl

instance : FunLike (DGRightModuleHom hM hN) M N where
  coe f := f.toLinearMap
  coe_injective _f _g hfg := toLinearMap_injective <| LinearMap.ext fun x ↦ congrFun hfg x

instance : GradedFunLike (DGRightModuleHom hM hN) ℳ ℳN where
  map_mem f := f.map_mem'

instance : LinearMapClass (DGRightModuleHom hM hN) Aᵐᵒᵖ M N where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

instance : CoeOut (DGRightModuleHom hM hN) (M →ₗ[Aᵐᵒᵖ] N) := ⟨toLinearMap⟩

@[simp]
theorem coe_toLinearMap (f : DGRightModuleHom hM hN) : ⇑f.toLinearMap = f := rfl

@[simp]
theorem coe_mk (f : M →ₗ[Aᵐᵒᵖ] N) (hf) (hdf) :
    ⇑(DGRightModuleHom.mk f hf hdf : DGRightModuleHom hM hN) = f := rfl

/-- Two DG right-module morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : DGRightModuleHom hM hN} (hfg : ∀ x, f x = g x) : f = g :=
  toLinearMap_injective <| LinearMap.ext hfg

/-- A DG right-module morphism commutes with the differentials. -/
@[simp]
theorem map_d (f : DGRightModuleHom hM hN) (x : M) : dN (f x) = f (dM x) :=
  f.map_d' x

/-- The identity morphism of a differential graded right module. -/
protected def id (hM : IsDGRightModule h ℳ dM) : DGRightModuleHom hM hM where
  toLinearMap := LinearMap.id
  map_mem' hx := hx
  map_d' _ := rfl

@[simp]
theorem id_toLinearMap (hM : IsDGRightModule h ℳ dM) :
    (DGRightModuleHom.id hM).toLinearMap = LinearMap.id := (rfl)

@[simp]
theorem coe_id (hM : IsDGRightModule h ℳ dM) :
    ⇑(DGRightModuleHom.id hM) = _root_.id := (rfl)

@[simp]
theorem id_apply (hM : IsDGRightModule h ℳ dM) (x : M) :
    DGRightModuleHom.id hM x = x := (rfl)

/-- Composition of morphisms of differential graded right modules. -/
def comp (g : DGRightModuleHom hN hP) (f : DGRightModuleHom hM hN) :
    DGRightModuleHom hM hP where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_mem' hx := Graded.map_mem g (Graded.map_mem f hx)
  map_d' x := by
    calc
      dP (g.toLinearMap (f.toLinearMap x)) = g.toLinearMap (dN (f.toLinearMap x)) :=
        g.map_d' (f.toLinearMap x)
      _ = g.toLinearMap (f.toLinearMap (dM x)) := congrArg g.toLinearMap (f.map_d' x)

@[simp]
theorem comp_toLinearMap (g : DGRightModuleHom hN hP) (f : DGRightModuleHom hM hN) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := (rfl)

@[simp]
theorem coe_comp (g : DGRightModuleHom hN hP) (f : DGRightModuleHom hM hN) :
    ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : DGRightModuleHom hN hP) (f : DGRightModuleHom hM hN) (x : M) :
    g.comp f x = g (f x) := (rfl)

/-- Composing a DG right-module morphism on the right with the identity morphism of its
source leaves it unchanged. -/
@[simp]
theorem comp_id (f : DGRightModuleHom hM hN) : f.comp (DGRightModuleHom.id hM) = f := by
  ext x
  rfl

/-- Composing a DG right-module morphism on the left with the identity morphism of its
target leaves it unchanged. -/
@[simp]
theorem id_comp (f : DGRightModuleHom hM hN) : (DGRightModuleHom.id hN).comp f = f := by
  ext x
  rfl

/-- Composition of DG right-module morphisms is associative. -/
@[simp]
theorem comp_assoc {Q : Type*} [AddCommGroup Q] [Module R Q] [Module Aᵐᵒᵖ Q]
    [IsScalarTower R Aᵐᵒᵖ Q] {ℳQ : ℤ → Submodule R Q}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳQ]
    [DirectSum.Decomposition ℳQ]
    {dQ : Q →ₗ[R] Q} {hQ : IsDGRightModule h ℳQ dQ}
    (k : DGRightModuleHom hP hQ) (g : DGRightModuleHom hN hP)
    (f : DGRightModuleHom hM hN) : (k.comp g).comp f = k.comp (g.comp f) := by
  ext x
  rfl

end DGRightModuleHom

end TauCeti
