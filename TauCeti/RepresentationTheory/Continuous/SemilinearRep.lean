/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.MulDistribMulAction
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep

/-!
# Continuous semilinear representations

Let a monoid `G` with a topology act on a semiring `B` by ring endomorphisms
(`MulSemiringAction G B`). A *continuous semilinear representation* of `G` on a `B`-module `W`
with a topology is an action of `G` on `W` by additive maps which is semilinear,
`g • (b • w) = (g • b) • (g • w)`, and jointly continuous on `G × W`.

These are Fontaine's `B`-representations of a Galois group `G_K` acting on a period ring `B`. For
`B = ℂ_p`, on which each element of the absolute Galois group `G_K` of `K` acts by its extension
by continuity, they are the semilinear `ℂ_p`-representations whose equivariant maps Fontaine's
full faithfulness theorem controls; for `B = B_dR⁺` they are the semilinear
`B_dR⁺`-representations. Forgetting the `B`-module structure down to the scalars `R` fixed by `G`
(`ℚ_p` for `ℂ_p`) leaves a jointly continuous `R`-linear representation,
`TauCeti.SemilinearRep.toContinuousRep`.

The action is bundled data, not an instance, because one module routinely carries several
semilinear actions: `ℂ_p` with its Galois action and with that action twisted by the cyclotomic
character are different representations on the same line, with no nonzero equivariant
`ℂ_p`-linear map between them for `K` finite over `ℚ_p`, by Tate's theorem `H⁰(G_K, ℂ_p(1)) = 0`.

## Main definitions

* `TauCeti.SemilinearRep G B W`: a jointly continuous semilinear action of `G` on `W`.
* `TauCeti.SemilinearRep.ofSMulDistribClass`, `TauCeti.SemilinearRep.self`: the representation
  given by a continuous semilinear `G`-action on `W`, in particular the action of `G` on `B`.
* `TauCeti.SemilinearRep.toContinuousRep`: the underlying linear representation over a ring `R`
  of scalars fixed by `G`.
* `TauCeti.SemilinearRep.twist`: the twist by a continuous character `G →ₜ* R`, as in the Tate
  twists `ℂ_p(j)`.
* `TauCeti.SemilinearRep.subrepresentation`, `TauCeti.SemilinearRep.prod`,
  `TauCeti.SemilinearRep.pi`: invariant submodules, binary products and arbitrary products.
* `TauCeti.SemilinearRep.Hom`: equivariant continuous `B`-linear maps, with identities,
  composition, `TauCeti.SemilinearRep.Hom.ofLinearMap` for sources with the module topology, the
  kernel and image representations `TauCeti.SemilinearRep.Hom.kerRep` and
  `TauCeti.SemilinearRep.Hom.rangeRep`, the lift `TauCeti.SemilinearRep.Hom.liftKerRep` into a
  kernel, the maps `TauCeti.SemilinearRep.Hom.prod` and `TauCeti.SemilinearRep.Hom.pi` into
  products, and the copairing `TauCeti.SemilinearRep.Hom.coprod` out of a direct sum.

## Main results

* `TauCeti.SemilinearRep.act_smul_of_tower`: the action is linear over the scalars fixed by `G`.
* `TauCeti.SemilinearRep.twist_one`, `TauCeti.SemilinearRep.twist_twist`: twisting by the trivial
  character does nothing, and successive twists multiply the characters.
* `TauCeti.SemilinearRep.Hom.kerRep_ext`, `TauCeti.SemilinearRep.Hom.ext_fst_snd`,
  `TauCeti.SemilinearRep.Hom.ext_proj`, `TauCeti.SemilinearRep.Hom.prod_ext`: morphisms into a
  kernel, into a direct sum or product, or out of a direct sum are determined by their composites
  with the structure maps, so the lifts and (co)pairings above are unique.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Doc. Math. Extra Vol. Kato (2003), §1.3.
-/

public section

namespace TauCeti

/-- **A continuous semilinear representation** of the monoid `G` with a topology on the
`B`-module `W` with a topology, where `G` acts on the semiring `B` by ring endomorphisms: an action
of `G` on `W` by additive maps that is semilinear, `g (b w) = (g • b) (g w)`, and whose action map
`G × W → W` is continuous. No topology on `B` is involved in the definition. -/
structure SemilinearRep (G B W : Type*) [Monoid G] [TopologicalSpace G] [Semiring B]
    [MulSemiringAction G B] [AddCommMonoid W] [Module B W] [TopologicalSpace W] where
  /-- The action of `G` on `W` by additive endomorphisms. -/
  act : G →* AddMonoid.End W
  /-- Semilinearity: `g (b w) = (g • b) (g w)`. -/
  act_smul (g : G) (b : B) (w : W) : act g (b • w) = (g • b) • act g w
  /-- Joint continuity of the action map `G × W → W`. -/
  continuous_act : Continuous fun x : G × W => act x.1 x.2

namespace SemilinearRep

variable {G B W W₁ W₂ W₃ : Type*} [Monoid G] [TopologicalSpace G] [Semiring B]
  [MulSemiringAction G B]
  [AddCommMonoid W] [Module B W] [TopologicalSpace W]
  [AddCommMonoid W₁] [Module B W₁] [TopologicalSpace W₁]
  [AddCommMonoid W₂] [Module B W₂] [TopologicalSpace W₂]
  [AddCommMonoid W₃] [Module B W₃] [TopologicalSpace W₃]

section Basic

/-- Two semilinear representations with the same action are equal. -/
@[ext]
theorem ext {ρ σ : SemilinearRep G B W} (h : ∀ g w, ρ.act g w = σ.act g w) : ρ = σ := by
  obtain ⟨ρ, _, _⟩ := ρ
  obtain ⟨σ, _, _⟩ := σ
  congr
  ext g w
  exact h g w

variable (ρ : SemilinearRep G B W)

theorem act_one_apply (w : W) : ρ.act 1 w = w := by
  rw [map_one, AddMonoid.End.coe_one, id]

theorem act_mul_apply (g h : G) (w : W) : ρ.act (g * h) w = ρ.act g (ρ.act h w) := by
  rw [map_mul, AddMonoid.End.coe_mul, Function.comp_apply]

/-- **Joint continuity in the form `fun_prop` uses.** If `f : X → G` and `v : X → W` are
continuous, then so is `x ↦ ρ.act (f x) (v x)`. -/
@[fun_prop]
theorem _root_.Continuous.semilinearRep_act {X : Type*} [TopologicalSpace X]
    (ρ : SemilinearRep G B W) {f : X → G} {v : X → W} (hf : Continuous f) (hv : Continuous v) :
    Continuous fun x => ρ.act (f x) (v x) :=
  ρ.continuous_act.comp (hf.prodMk hv)

/-- Each element of `G` acts by a continuous map. -/
@[fun_prop]
theorem continuous_act_apply (g : G) : Continuous (ρ.act g) := by
  fun_prop

/-- The orbit map `g ↦ ρ.act g w` is continuous. -/
@[fun_prop]
theorem continuous_orbit (w : W) : Continuous fun g => ρ.act g w := by
  fun_prop

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [MulSemiringAction G B]
  (ρ : SemilinearRep G B W)

@[simp]
theorem act_inv_act (g : G) (w : W) : ρ.act g⁻¹ (ρ.act g w) = w := by
  rw [← act_mul_apply, inv_mul_cancel, act_one_apply]

@[simp]
theorem act_act_inv (g : G) (w : W) : ρ.act g (ρ.act g⁻¹ w) = w := by
  rw [← act_mul_apply, mul_inv_cancel, act_one_apply]

end Group

end Basic

section Construction

/-- Build a semilinear representation from its action map `G → W → W` and the laws it satisfies.
This lets each construction state its action by a formula. -/
def mk' (a : G → W → W) (map_zero : ∀ g, a g 0 = 0)
    (map_add : ∀ g v w, a g (v + w) = a g v + a g w) (one : ∀ w, a 1 w = w)
    (mul : ∀ g h w, a (g * h) w = a g (a h w)) (smul : ∀ g (b : B) w, a g (b • w) = (g • b) • a g w)
    (cont : Continuous fun x : G × W => a x.1 x.2) : SemilinearRep G B W where
  act :=
    { toFun g := { toFun := a g, map_zero' := map_zero g, map_add' := map_add g }
      map_one' := AddMonoidHom.ext one
      map_mul' g h := AddMonoidHom.ext (mul g h) }
  act_smul := smul
  continuous_act := cont

@[simp]
theorem mk'_act (a : G → W → W) (map_zero : ∀ g, a g 0 = 0)
    (map_add : ∀ g v w, a g (v + w) = a g v + a g w) (one : ∀ w, a 1 w = w)
    (mul : ∀ g h w, a (g * h) w = a g (a h w))
    (smul : ∀ g (b : B) w, a g (b • w) = (g • b) • a g w)
    (cont : Continuous fun x : G × W => a x.1 x.2) (g : G) (w : W) :
    (mk' a map_zero map_add one mul smul cont).act g w = a g w :=
  (rfl)

end Construction

section OfSMulDistribClass

variable (G B W) in
/-- The semilinear representation given by a jointly continuous semilinear action of `G` on `W`,
in Mathlib's unbundled form. -/
def ofSMulDistribClass [DistribMulAction G W] [SMulDistribClass G B W] [ContinuousSMul G W] :
    SemilinearRep G B W where
  act := DistribMulAction.toAddMonoidEnd G W
  act_smul := smul_distrib_smul
  continuous_act := continuous_smul

@[simp]
theorem ofSMulDistribClass_act [DistribMulAction G W] [SMulDistribClass G B W]
    [ContinuousSMul G W] (g : G) (w : W) : (ofSMulDistribClass G B W).act g w = g • w :=
  (rfl)

variable (G B) in
/-- The action of `G` on the semiring `B` itself, as a semilinear representation on the free
`B`-module of rank one. For the Galois action on `ℂ_p` this is the basic representation `ℂ_p`. -/
abbrev self [TopologicalSpace B] [ContinuousSMul G B] : SemilinearRep G B B :=
  ofSMulDistribClass G B B

end OfSMulDistribClass

section FixedScalars

variable {R : Type*} [CommSemiring R] [Algebra R B] [SMulCommClass G R B]
  [Module R W] [IsScalarTower R B W]

/-- **A semilinear action is linear over the fixed scalars.** If `G` fixes the image of `R` in `B`,
then `G` acts `R`-linearly on every semilinear representation; for `B = ℂ_p` this is
`ℚ_p`-linearity. -/
theorem act_smul_of_tower (ρ : SemilinearRep G B W) (g : G) (r : R) (w : W) :
    ρ.act g (r • w) = r • ρ.act g w := by
  rw [← algebraMap_smul B r w, ρ.act_smul, smul_algebraMap, algebraMap_smul]

variable (R) in
/-- The jointly continuous `R`-linear representation underlying a semilinear representation, for
scalars `R` fixed by `G`. For `B = ℂ_p` and `R = ℚ_p` this is the underlying `ℚ_p`-representation
of a semilinear `ℂ_p`-representation. -/
def toContinuousRep (ρ : SemilinearRep G B W) : ContinuousRep G R W where
  toRepresentation :=
    { toFun g :=
        { toFun := ρ.act g
          map_add' := map_add (ρ.act g)
          map_smul' := ρ.act_smul_of_tower g }
      map_one' := LinearMap.ext ρ.act_one_apply
      map_mul' g h := LinearMap.ext (ρ.act_mul_apply g h) }
  continuous_action := ρ.continuous_act

@[simp]
theorem toContinuousRep_apply (ρ : SemilinearRep G B W) (g : G) (w : W) :
    ρ.toContinuousRep R g w = ρ.act g w :=
  (rfl)

end FixedScalars

section Twist

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [Algebra R B] [SMulCommClass G R B]
  [Module R W] [IsScalarTower R B W] [ContinuousSMul R W]

/-- **The twist of a semilinear representation by a continuous character** `χ : G →ₜ* R` with
values in scalars fixed by `G`: `g` acts by `w ↦ χ g • ρ.act g w`. Twisting the Galois action on
`ℂ_p` by the `j`-th power of the cyclotomic character gives the Tate twist `ℂ_p(j)`. -/
def twist (ρ : SemilinearRep G B W) (χ : G →ₜ* R) : SemilinearRep G B W :=
  mk' (fun g w => χ g • ρ.act g w) (fun g => by simp) (fun g v w => by simp [smul_add])
    (fun w => by simp) (fun g h w => by simp [ρ.act_smul_of_tower, mul_smul])
    (fun g b w => by rw [ρ.act_smul, smul_comm])
    ((χ.continuous.comp continuous_fst).smul ρ.continuous_act)

@[simp]
theorem twist_act (ρ : SemilinearRep G B W) (χ : G →ₜ* R) (g : G) (w : W) :
    (ρ.twist χ).act g w = χ g • ρ.act g w :=
  (rfl)

/-- Twisting by the trivial character gives back the representation. -/
@[simp]
theorem twist_one (ρ : SemilinearRep G B W) : ρ.twist (1 : G →ₜ* R) = ρ := by
  ext g w
  simp

/-- Twisting by `χ` and then by `ψ` is twisting by `ψ * χ`. -/
@[simp]
theorem twist_twist [ContinuousMul R] (ρ : SemilinearRep G B W) (χ ψ : G →ₜ* R) :
    (ρ.twist χ).twist ψ = ρ.twist (ψ * χ) := by
  ext g w
  simp [mul_smul]

end Twist

section Subrepresentation

/-- The restriction of a semilinear representation to a `G`-stable `B`-submodule, with the
subspace topology. -/
def subrepresentation (ρ : SemilinearRep G B W) (N : Submodule B W)
    (hN : ∀ g, ∀ w ∈ N, ρ.act g w ∈ N) : SemilinearRep G B N :=
  mk' (fun g w => ⟨ρ.act g (w : W), hN g _ w.property⟩)
    (fun g => Subtype.ext (map_zero (ρ.act g)))
    (fun g v w => Subtype.ext (map_add (ρ.act g) v.val w.val))
    (fun w => Subtype.ext (ρ.act_one_apply w.val))
    (fun g h w => Subtype.ext (ρ.act_mul_apply g h w.val))
    (fun g b w => Subtype.ext (ρ.act_smul g b w.val))
    ((ρ.continuous_act.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _)

@[simp]
theorem coe_subrepresentation_act (ρ : SemilinearRep G B W) (N : Submodule B W)
    (hN : ∀ g, ∀ w ∈ N, ρ.act g w ∈ N) (g : G) (w : N) :
    ((ρ.subrepresentation N hN).act g w : W) = ρ.act g w :=
  (rfl)

end Subrepresentation

section Prod

/-- **The direct sum of two semilinear representations**: `G` acts componentwise on `W₁ × W₂`,
with the product topology. -/
def prod (ρ₁ : SemilinearRep G B W₁) (ρ₂ : SemilinearRep G B W₂) :
    SemilinearRep G B (W₁ × W₂) :=
  mk' (fun g w => (ρ₁.act g w.1, ρ₂.act g w.2)) (fun g => by simp) (fun g v w => by simp)
    (fun w => by simp) (fun g h w => by simp)
    (fun g b w => by simp [ρ₁.act_smul, ρ₂.act_smul]) (by fun_prop)

@[simp]
theorem prod_act (ρ₁ : SemilinearRep G B W₁) (ρ₂ : SemilinearRep G B W₂) (g : G)
    (w : W₁ × W₂) : (ρ₁.prod ρ₂).act g w = (ρ₁.act g w.1, ρ₂.act g w.2) :=
  (rfl)

end Prod

section Pi

variable {ι : Type*} {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module B (V i)]
  [∀ i, TopologicalSpace (V i)]

/-- **The product of a family of semilinear representations**: `G` acts componentwise on
`∀ i, V i`, with the product topology. For a finite index type this is the finite direct sum. -/
def pi (ρ : ∀ i, SemilinearRep G B (V i)) : SemilinearRep G B (∀ i, V i) :=
  mk' (fun g w i => (ρ i).act g (w i)) (fun g => by ext; simp) (fun g v w => by ext; simp)
    (fun w => by ext; simp) (fun g h w => by ext; simp)
    (fun g b w => by ext i; simp [(ρ i).act_smul]) (continuous_pi fun i => by fun_prop)

@[simp]
theorem pi_act (ρ : ∀ i, SemilinearRep G B (V i)) (g : G) (w : ∀ i, V i) (i : ι) :
    (pi ρ).act g w i = (ρ i).act g (w i) :=
  (rfl)

end Pi

/-- **A morphism of semilinear representations**: a continuous `B`-linear map commuting with the
actions of `G`. -/
structure Hom (ρ₁ : SemilinearRep G B W₁) (ρ₂ : SemilinearRep G B W₂) extends W₁ →L[B] W₂ where
  /-- Equivariance: `f (g w) = g (f w)`. -/
  map_act' (g : G) (w : W₁) : toFun (ρ₁.act g w) = ρ₂.act g (toFun w)

/-- The continuous linear map underlying a morphism of semilinear representations. -/
add_decl_doc Hom.toContinuousLinearMap

namespace Hom

variable {ρ : SemilinearRep G B W} {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂}
  {ρ₃ : SemilinearRep G B W₃}

instance : FunLike (Hom ρ₁ ρ₂) W₁ W₂ where
  coe f := f.toFun
  coe_injective f f' h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := f'
    congr

instance : ContinuousSemilinearMapClass (Hom ρ₁ ρ₂) (RingHom.id B) W₁ W₂ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous f := f.cont

@[simp]
theorem coe_toContinuousLinearMap (f : Hom ρ₁ ρ₂) : ⇑f.toContinuousLinearMap = f :=
  (rfl)

@[simp]
theorem coe_mk (f : W₁ →L[B] W₂) (h : ∀ g w, f (ρ₁.act g w) = ρ₂.act g (f w)) :
    ⇑(⟨f, h⟩ : Hom ρ₁ ρ₂) = f :=
  (rfl)

@[ext]
theorem ext {f f' : Hom ρ₁ ρ₂} (h : ∀ w, f w = f' w) : f = f' :=
  DFunLike.ext _ _ h

/-- **Equivariance** of a morphism of semilinear representations. -/
@[simp]
theorem map_act (f : Hom ρ₁ ρ₂) (g : G) (w : W₁) : f (ρ₁.act g w) = ρ₂.act g (f w) :=
  f.map_act' g w

/-- An equivariant `B`-linear map out of a module with the module topology is a morphism of
semilinear representations: it is automatically continuous. -/
def ofLinearMap [TopologicalSpace B] [IsModuleTopology B W₁] [ContinuousAdd W₂]
    [ContinuousSMul B W₂] (f : W₁ →ₗ[B] W₂) (h : ∀ g w, f (ρ₁.act g w) = ρ₂.act g (f w)) :
    Hom ρ₁ ρ₂ :=
  ⟨⟨f, IsModuleTopology.continuous_of_linearMap f⟩, h⟩

@[simp]
theorem coe_ofLinearMap [TopologicalSpace B] [IsModuleTopology B W₁] [ContinuousAdd W₂]
    [ContinuousSMul B W₂] (f : W₁ →ₗ[B] W₂) (h : ∀ g w, f (ρ₁.act g w) = ρ₂.act g (f w)) :
    ⇑(ofLinearMap f h : Hom ρ₁ ρ₂) = f :=
  (rfl)

variable (ρ) in
/-- The identity morphism. -/
def id : Hom ρ ρ :=
  ⟨.id B W, fun _ _ => rfl⟩

@[simp]
theorem id_apply (w : W) : id ρ w = w :=
  (rfl)

/-- The composite of two morphisms. -/
def comp (f' : Hom ρ₂ ρ₃) (f : Hom ρ₁ ρ₂) : Hom ρ₁ ρ₃ :=
  ⟨f'.toContinuousLinearMap.comp f.toContinuousLinearMap, fun g w => by simp⟩

@[simp]
theorem comp_apply (f' : Hom ρ₂ ρ₃) (f : Hom ρ₁ ρ₂) (w : W₁) : f'.comp f w = f' (f w) :=
  (rfl)

@[simp]
theorem id_comp (f : Hom ρ₁ ρ₂) : (id ρ₂).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : Hom ρ₁ ρ₂) : f.comp (id ρ₁) = f :=
  ext fun _ => rfl

theorem comp_assoc {W₄ : Type*} [AddCommMonoid W₄] [Module B W₄] [TopologicalSpace W₄]
    {ρ₄ : SemilinearRep G B W₄} (f'' : Hom ρ₃ ρ₄) (f' : Hom ρ₂ ρ₃) (f : Hom ρ₁ ρ₂) :
    (f''.comp f').comp f = f''.comp (f'.comp f) :=
  ext fun _ => rfl

/-- The zero morphism. -/
instance : Zero (Hom ρ₁ ρ₂) :=
  ⟨⟨0, fun g w => by simp⟩⟩

@[simp]
theorem zero_apply (w : W₁) : (0 : Hom ρ₁ ρ₂) w = 0 :=
  (rfl)

@[simp]
theorem comp_zero (f : Hom ρ₂ ρ₃) : f.comp (0 : Hom ρ₁ ρ₂) = 0 :=
  ext fun _ => by simp

@[simp]
theorem zero_comp (f : Hom ρ₁ ρ₂) : (0 : Hom ρ₂ ρ₃).comp f = 0 :=
  ext fun _ => rfl

/-- The kernel of a morphism is stable under `G`. -/
theorem act_mem_ker (f : Hom ρ₁ ρ₂) (g : G) {w : W₁}
    (hw : w ∈ LinearMap.ker (f : W₁ →ₗ[B] W₂)) :
    ρ₁.act g w ∈ LinearMap.ker (f : W₁ →ₗ[B] W₂) := by
  simp_all [LinearMap.mem_ker]

/-- The image of a morphism is stable under `G`. -/
theorem act_mem_range (f : Hom ρ₁ ρ₂) (g : G) {w : W₂}
    (hw : w ∈ LinearMap.range (f : W₁ →ₗ[B] W₂)) :
    ρ₂.act g w ∈ LinearMap.range (f : W₁ →ₗ[B] W₂) := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨ρ₁.act g v, map_act f g v⟩

/-- **The kernel representation** of a morphism: the action of `G` on its kernel, with the
subspace topology. -/
def kerRep (f : Hom ρ₁ ρ₂) : SemilinearRep G B (LinearMap.ker (f : W₁ →ₗ[B] W₂)) :=
  ρ₁.subrepresentation (LinearMap.ker (f : W₁ →ₗ[B] W₂)) fun g _ hw => f.act_mem_ker g hw

/-- **The image representation** of a morphism: the action of `G` on its image, with the
subspace topology. -/
def rangeRep (f : Hom ρ₁ ρ₂) : SemilinearRep G B (LinearMap.range (f : W₁ →ₗ[B] W₂)) :=
  ρ₂.subrepresentation (LinearMap.range (f : W₁ →ₗ[B] W₂)) fun g _ hw => f.act_mem_range g hw

@[simp]
theorem coe_kerRep_act (f : Hom ρ₁ ρ₂) (g : G) (w : LinearMap.ker (f : W₁ →ₗ[B] W₂)) :
    (f.kerRep.act g w : W₁) = ρ₁.act g w :=
  (rfl)

@[simp]
theorem coe_rangeRep_act (f : Hom ρ₁ ρ₂) (g : G) (w : LinearMap.range (f : W₁ →ₗ[B] W₂)) :
    (f.rangeRep.act g w : W₂) = ρ₂.act g w :=
  (rfl)

end Hom

section Morphisms

/-- The inclusion of a subrepresentation. -/
def subtype (ρ : SemilinearRep G B W) (N : Submodule B W) (hN : ∀ g, ∀ w ∈ N, ρ.act g w ∈ N) :
    Hom (ρ.subrepresentation N hN) ρ :=
  ⟨N.subtypeL, fun _ _ => rfl⟩

@[simp]
theorem subtype_apply (ρ : SemilinearRep G B W) (N : Submodule B W)
    (hN : ∀ g, ∀ w ∈ N, ρ.act g w ∈ N) (w : N) : ρ.subtype N hN w = w :=
  (rfl)

/-- The kernel representation of a morphism maps to its source. -/
def Hom.kerι {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) :
    Hom f.kerRep ρ₁ :=
  ρ₁.subtype _ _

/-- A morphism factors through its image representation. -/
def Hom.rangeRestrict {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) :
    Hom ρ₁ f.rangeRep :=
  ⟨f.toContinuousLinearMap.rangeRestrict, fun g w => Subtype.ext (f.map_act g w)⟩

@[simp]
theorem Hom.kerι_apply {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂)
    (w : LinearMap.ker (f : W₁ →ₗ[B] W₂)) : f.kerι w = w :=
  (rfl)

@[simp]
theorem Hom.coe_rangeRestrict_apply {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂}
    (f : Hom ρ₁ ρ₂) (w : W₁) : (f.rangeRestrict w : W₂) = f w :=
  (rfl)

/-- The image representation of a morphism maps to its target. -/
def Hom.rangeι {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) :
    Hom f.rangeRep ρ₂ :=
  ρ₂.subtype _ _

@[simp]
theorem Hom.rangeι_apply {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂)
    (w : LinearMap.range (f : W₁ →ₗ[B] W₂)) : f.rangeι w = w :=
  (rfl)

/-- A morphism is its corestriction to the image representation followed by the inclusion of the
image. -/
@[simp]
theorem Hom.rangeι_comp_rangeRestrict {ρ₁ : SemilinearRep G B W₁}
    {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) : f.rangeι.comp f.rangeRestrict = f :=
  Hom.ext fun _ => rfl

/-- A morphism vanishes on its kernel. -/
@[simp]
theorem Hom.map_coe_ker {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂)
    (w : LinearMap.ker (f : W₁ →ₗ[B] W₂)) : f (w : W₁) = 0 :=
  LinearMap.mem_ker.mp w.property

/-- A morphism composed with the inclusion of its kernel representation is zero. -/
@[simp]
theorem Hom.comp_kerι {ρ₁ : SemilinearRep G B W₁} {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) :
    f.comp f.kerι = 0 :=
  Hom.ext fun w => by simp

/-- **The universal property of the kernel**: a morphism `h` into the source of `f` with `f ∘ h = 0`
factors through the kernel representation of `f`. -/
def Hom.liftKerRep {ρ : SemilinearRep G B W} {ρ₁ : SemilinearRep G B W₁}
    {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) (h : Hom ρ ρ₁) (hh : f.comp h = 0) :
    Hom ρ f.kerRep :=
  ⟨h.toContinuousLinearMap.codRestrict _ fun w =>
      LinearMap.mem_ker.mpr (by simpa using DFunLike.congr_fun hh w),
    fun g w => Subtype.ext (by simp)⟩

@[simp]
theorem Hom.coe_liftKerRep_apply {ρ : SemilinearRep G B W} {ρ₁ : SemilinearRep G B W₁}
    {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) (h : Hom ρ ρ₁) (hh : f.comp h = 0) (w : W) :
    (f.liftKerRep h hh w : W₁) = h w :=
  (rfl)

@[simp]
theorem Hom.kerι_comp_liftKerRep {ρ : SemilinearRep G B W} {ρ₁ : SemilinearRep G B W₁}
    {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) (h : Hom ρ ρ₁) (hh : f.comp h = 0) :
    f.kerι.comp (f.liftKerRep h hh) = h :=
  Hom.ext fun _ => rfl

/-- **Uniqueness in the universal property of the kernel**: morphisms into the kernel
representation of `f` are determined by their composite with the inclusion `f.kerι`. -/
theorem Hom.kerRep_ext {ρ : SemilinearRep G B W} {ρ₁ : SemilinearRep G B W₁}
    {ρ₂ : SemilinearRep G B W₂} {f : Hom ρ₁ ρ₂} {k k' : Hom ρ f.kerRep}
    (h : f.kerι.comp k = f.kerι.comp k') : k = k' :=
  Hom.ext fun w => Subtype.ext (by simpa using DFunLike.congr_fun h w)

/-- `Hom.liftKerRep` is the only factorization through the kernel representation. -/
theorem Hom.liftKerRep_unique {ρ : SemilinearRep G B W} {ρ₁ : SemilinearRep G B W₁}
    {ρ₂ : SemilinearRep G B W₂} (f : Hom ρ₁ ρ₂) (h : Hom ρ ρ₁) (hh : f.comp h = 0)
    (k : Hom ρ f.kerRep) (hk : f.kerι.comp k = h) : k = f.liftKerRep h hh :=
  Hom.kerRep_ext (by rw [hk, kerι_comp_liftKerRep])

variable (ρ₁ : SemilinearRep G B W₁) (ρ₂ : SemilinearRep G B W₂)

/-- The first projection out of a direct sum. -/
def fst : Hom (ρ₁.prod ρ₂) ρ₁ :=
  ⟨.fst B W₁ W₂, fun _ _ => rfl⟩

/-- The second projection out of a direct sum. -/
def snd : Hom (ρ₁.prod ρ₂) ρ₂ :=
  ⟨.snd B W₁ W₂, fun _ _ => rfl⟩

/-- The first inclusion into a direct sum. -/
def inl : Hom ρ₁ (ρ₁.prod ρ₂) :=
  ⟨.inl B W₁ W₂, fun g w => by simp⟩

/-- The second inclusion into a direct sum. -/
def inr : Hom ρ₂ (ρ₁.prod ρ₂) :=
  ⟨.inr B W₁ W₂, fun g w => by simp⟩

@[simp]
theorem fst_apply (w : W₁ × W₂) : fst ρ₁ ρ₂ w = w.1 :=
  (rfl)

@[simp]
theorem snd_apply (w : W₁ × W₂) : snd ρ₁ ρ₂ w = w.2 :=
  (rfl)

@[simp]
theorem inl_apply (w : W₁) : inl ρ₁ ρ₂ w = (w, 0) :=
  (rfl)

@[simp]
theorem inr_apply (w : W₂) : inr ρ₁ ρ₂ w = (0, w) :=
  (rfl)

section HomProd

variable {ρ₁ ρ₂} {σ : SemilinearRep G B W}

/-- **The universal property of the direct sum**: two morphisms out of `σ` pair to a morphism into
the direct sum. -/
def Hom.prod (f : Hom σ ρ₁) (f' : Hom σ ρ₂) : Hom σ (ρ₁.prod ρ₂) :=
  ⟨f.toContinuousLinearMap.prod f'.toContinuousLinearMap, fun g w => by simp⟩

@[simp]
theorem Hom.prod_apply (f : Hom σ ρ₁) (f' : Hom σ ρ₂) (w : W) : f.prod f' w = (f w, f' w) :=
  (rfl)

@[simp]
theorem fst_comp_prod (f : Hom σ ρ₁) (f' : Hom σ ρ₂) : (fst ρ₁ ρ₂).comp (f.prod f') = f :=
  Hom.ext fun _ => rfl

@[simp]
theorem snd_comp_prod (f : Hom σ ρ₁) (f' : Hom σ ρ₂) : (snd ρ₁ ρ₂).comp (f.prod f') = f' :=
  Hom.ext fun _ => rfl

/-- **Uniqueness in the universal property of the direct sum**: morphisms into the direct sum are
determined by their composites with the two projections. -/
theorem Hom.ext_fst_snd {f f' : Hom σ (ρ₁.prod ρ₂)}
    (h₁ : (fst ρ₁ ρ₂).comp f = (fst ρ₁ ρ₂).comp f')
    (h₂ : (snd ρ₁ ρ₂).comp f = (snd ρ₁ ρ₂).comp f') : f = f' :=
  Hom.ext fun w =>
    Prod.ext (by simpa using DFunLike.congr_fun h₁ w) (by simpa using DFunLike.congr_fun h₂ w)

/-- **The universal property of the direct sum as a coproduct**: two morphisms into `σ` copair to
the morphism `(w₁, w₂) ↦ f w₁ + f' w₂` out of the direct sum. -/
def Hom.coprod [ContinuousAdd W] (f : Hom ρ₁ σ) (f' : Hom ρ₂ σ) : Hom (ρ₁.prod ρ₂) σ :=
  ⟨f.toContinuousLinearMap.coprod f'.toContinuousLinearMap, fun g w => by simp⟩

@[simp]
theorem Hom.coprod_apply [ContinuousAdd W] (f : Hom ρ₁ σ) (f' : Hom ρ₂ σ) (w : W₁ × W₂) :
    f.coprod f' w = f w.1 + f' w.2 :=
  (rfl)

@[simp]
theorem coprod_comp_inl [ContinuousAdd W] (f : Hom ρ₁ σ) (f' : Hom ρ₂ σ) :
    (f.coprod f').comp (inl ρ₁ ρ₂) = f :=
  Hom.ext fun _ => by simp

@[simp]
theorem coprod_comp_inr [ContinuousAdd W] (f : Hom ρ₁ σ) (f' : Hom ρ₂ σ) :
    (f.coprod f').comp (inr ρ₁ ρ₂) = f' :=
  Hom.ext fun _ => by simp

/-- **Uniqueness in the universal property of the direct sum as a coproduct**: morphisms out of the
direct sum are determined by their composites with the two inclusions. -/
theorem Hom.prod_ext {f f' : Hom (ρ₁.prod ρ₂) σ} (h₁ : f.comp (inl ρ₁ ρ₂) = f'.comp (inl ρ₁ ρ₂))
    (h₂ : f.comp (inr ρ₁ ρ₂) = f'.comp (inr ρ₁ ρ₂)) : f = f' :=
  Hom.ext fun w => by
    have e₁ := DFunLike.congr_fun h₁ w.1
    have e₂ := DFunLike.congr_fun h₂ w.2
    simp only [comp_apply, inl_apply, inr_apply] at e₁ e₂
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hw, map_add, map_add, e₁, e₂]

end HomProd

@[simp]
theorem fst_comp_inl : (fst ρ₁ ρ₂).comp (inl ρ₁ ρ₂) = Hom.id ρ₁ :=
  Hom.ext fun _ => rfl

@[simp]
theorem snd_comp_inr : (snd ρ₁ ρ₂).comp (inr ρ₁ ρ₂) = Hom.id ρ₂ :=
  Hom.ext fun _ => rfl

@[simp]
theorem fst_comp_inr : (fst ρ₁ ρ₂).comp (inr ρ₁ ρ₂) = 0 :=
  Hom.ext fun _ => rfl

@[simp]
theorem snd_comp_inl : (snd ρ₁ ρ₂).comp (inl ρ₁ ρ₂) = 0 :=
  Hom.ext fun _ => rfl

variable {ι : Type*} {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module B (V i)]
  [∀ i, TopologicalSpace (V i)] (ρ : ∀ i, SemilinearRep G B (V i))

/-- The projection out of a product onto one factor. -/
def proj (i : ι) : Hom (pi ρ) (ρ i) :=
  ⟨.proj i, fun _ _ => rfl⟩

@[simp]
theorem proj_apply (i : ι) (w : ∀ i, V i) : proj ρ i w = w i :=
  (rfl)

/-- The inclusion of one factor into a product. -/
def single [DecidableEq ι] (i : ι) : Hom (ρ i) (pi ρ) :=
  ⟨.single B V i, fun g w => by
    ext j
    obtain rfl | hj := eq_or_ne j i <;> simp [*]⟩

@[simp]
theorem single_apply [DecidableEq ι] (i : ι) (w : V i) : single ρ i w = Pi.single i w :=
  (rfl)

@[simp]
theorem proj_comp_single [DecidableEq ι] (i : ι) : (proj ρ i).comp (single ρ i) = Hom.id (ρ i) :=
  Hom.ext fun _ => by simp

section HomPi

variable {ρ} {σ : SemilinearRep G B W}

/-- **The universal property of the product**: a family of morphisms out of `σ` gives a morphism
into the product. -/
def Hom.pi (f : ∀ i, Hom σ (ρ i)) : Hom σ (SemilinearRep.pi ρ) :=
  ⟨ContinuousLinearMap.pi fun i => (f i).toContinuousLinearMap, fun g w => by ext i; simp⟩

@[simp]
theorem Hom.pi_apply (f : ∀ i, Hom σ (ρ i)) (w : W) (i : ι) : Hom.pi f w i = f i w :=
  (rfl)

@[simp]
theorem proj_pi (f : ∀ i, Hom σ (ρ i)) (i : ι) : (proj ρ i).comp (Hom.pi f) = f i :=
  Hom.ext fun _ => rfl

/-- **Uniqueness in the universal property of the product**: morphisms into the product are
determined by their composites with the projections. -/
theorem Hom.ext_proj {f f' : Hom σ (SemilinearRep.pi ρ)}
    (h : ∀ i, (proj ρ i).comp f = (proj ρ i).comp f') : f = f' :=
  Hom.ext fun w => funext fun i => by simpa using DFunLike.congr_fun (h i) w

end HomPi

end Morphisms

end SemilinearRep

end TauCeti
