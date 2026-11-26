/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Patching.PatchedModule

import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Algebra.Ring.SquareZero
import TauCeti.Logic.Function.Basic

/-!
# Milnor patching of finitely generated projective modules

Consider a commutative square of possibly noncommutative rings `π₁ ∘ p₁ = π₂ ∘ p₂`, with
`p₁ : D → A₁`, `p₂ : D → A₂`, `π₁ : A₁ → Q` and `π₂ : A₂ → Q`, which is a fibre product: every
pair `(a₁, a₂)` with `π₁ a₁ = π₂ a₂` comes from exactly one element of `D`. A patching triple
`(P₁, P₂, α)` consists of a left `A₁`-module `P₁`, a left `A₂`-module `P₂` and a `Q`-linear
isomorphism `α : Q ⊗_{A₁} P₁ ≃ Q ⊗_{A₂} P₂`; its patched module is
`M = {(x, y) ∈ P₁ × P₂ | α (1 ⊗ x) = 1 ⊗ y}` (`TauCeti.PatchedModule`).

This file proves the half of Milnor's patching theorem that constructs modules over `D`: when
`π₁` or `π₂` is surjective and `P₁`, `P₂` are finitely generated projective, the patched module
`M` is a finitely generated projective `D`-module, and the comparison maps
`A₁ ⊗_D M → P₁` and `A₂ ⊗_D M → P₂`, `s ⊗ (x, y) ↦ s • x` and `s ⊗ (x, y) ↦ s • y`, are
isomorphisms. They identify the patching triple `(A₁ ⊗_D M, A₂ ⊗_D M, α_M)` of `M` with
`(P₁, P₂, α)`, compatibly with the gluing isomorphisms
(`TauCeti.PatchedModule.map_compareSnd_commSqEquiv`). Together with full faithfulness
(`TauCeti.BalancedExtension.existsUnique_map_eq_and_map_eq`), this says that extension of
scalars from `D` to patching triples is an equivalence on finitely generated projective modules.
Applied to the square of opposite rings, it describes finitely generated projective right modules
over a fibre product of rings, as used for the Mayer–Vietoris sequence of algebraic `K₀` and `K₁`.

## Main definitions

* `TauCeti.PatchedModule.compareFst h α`, `TauCeti.PatchedModule.compareSnd h α`: the
  comparison maps `A₁ ⊗_D M → P₁` and `A₂ ⊗_D M → P₂`.
* `TauCeti.PatchedModule.compareFstEquiv`, `TauCeti.PatchedModule.compareSndEquiv`: these
  maps as isomorphisms, for finitely generated projective triples with a surjective leg.

## Main results

* `TauCeti.PatchedModule.map_compareSnd_commSqEquiv`: the comparison maps intertwine the
  gluing isomorphism of `M` with `α`.
* `TauCeti.finite_patchedModule`, `TauCeti.projective_patchedModule`: with one surjective leg,
  the patched module of a finitely generated projective triple is finitely generated projective.
* `TauCeti.PatchedModule.bijective_compareFst`, `TauCeti.PatchedModule.bijective_compareSnd`:
  its comparison maps are bijective.

## Implementation notes

Following Milnor, the proof reduces an arbitrary triple to the triple `(A₁ ⊗_D F, A₂ ⊗_D F, α_F)`
of a finitely generated free `D`-module `F`, whose patched module is `F` itself
(`TauCeti.bijective_toPatchedModule`). The conclusions pass to retracts of triples, so it suffices
to exhibit `(P₁, P₂, α)` as a retract of such a triple. Say `π₁` is surjective, and write `P₁` and
`P₂` as retracts of `A₁ ⊗_D G₁` and `A₂ ⊗_D G₂` for finite free `G₁`, `G₂`. Over `Q`, the
isomorphism `α` and its inverse give maps `y : Q ⊗ G₁ → Q ⊗ G₂` and `x : Q ⊗ G₂ → Q ⊗ G₁` between
the extensions of `G₁` and `G₂` (both identified with modules over `D` through the gluing
isomorphisms), and the triple embeds into the triple of `F = G₁ × G₂` along the automorphism
`(1 + X) (1 + Y) (1 + X)` of `Q ⊗ F`, where `X = [[0, x], [0, 0]]` and `Y = [[0, 0], [y, 0]]`
are block unipotent. This is the form of Whitehead's factorization of `diag(u, u⁻¹)` into
elementary matrices used by Milnor. Because `π₁` is surjective, `x` and `y` lift to `A₁`-linear
maps (`TauCeti.BalancedExtension.exists_map_eq_of_surjective`), so the automorphism lifts to
`A₁ ⊗_D F` and the embedding becomes a retract of the triple of `F`. The case of a surjective `π₂`
follows by exchanging the two sides of the square.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72, Princeton
  University Press (1971), §2 (the modules `M(P₁, P₂, h)` over a fibre product of rings: they are
  finitely generated projective, with `Λⱼ ⊗ M ≅ Pⱼ`, when one of the two maps is surjective).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, Theorem 2.7 (Milnor patching).
-/

public section

namespace TauCeti

open BalancedExtension

variable {D A₁ A₂ Q : Type*} [Ring D] [Ring A₁] [Ring A₂] [Ring Q]
  {p₁ : D →+* A₁} {p₂ : D →+* A₂} {π₁ : A₁ →+* Q} {π₂ : A₂ →+* Q}

namespace PatchedModule

section Compare

variable {P₁ P₂ : Type*} [AddCommGroup P₁] [Module A₁ P₁] [AddCommGroup P₂] [Module A₂ P₂]
  (h : π₁.comp p₁ = π₂.comp p₂) (α : BalancedExtension π₁ P₁ →ₗ[Q] BalancedExtension π₂ P₂)

/-- The comparison map `A₁ ⊗_D M(P₁, P₂, α) → P₁`, `s ⊗ (x, y) ↦ s • x`, induced by the first
projection of the patched module. -/
def compareFst : BalancedExtension p₁ (PatchedModule h α) →ₗ[A₁] P₁ :=
  BalancedExtension.lift (fstHom h α)

/-- The comparison map `A₂ ⊗_D M(P₁, P₂, α) → P₂`, `s ⊗ (x, y) ↦ s • y`, induced by the second
projection of the patched module. -/
def compareSnd : BalancedExtension p₂ (PatchedModule h α) →ₗ[A₂] P₂ :=
  BalancedExtension.lift (sndHom h α)

@[simp]
theorem compareFst_tmul (s : A₁) (x : PatchedModule h α) :
    compareFst h α (tmul p₁ s x) = s • x.fst := by
  simp [compareFst]

@[simp]
theorem compareSnd_tmul (s : A₂) (x : PatchedModule h α) :
    compareSnd h α (tmul p₂ s x) = s • x.snd := by
  simp [compareSnd]

/-- The comparison maps form a morphism from the patching triple `(A₁ ⊗_D M, A₂ ⊗_D M, α_M)` of
the patched module `M = M(P₁, P₂, α)` to `(P₁, P₂, α)`: they intertwine the gluing isomorphism
`α_M` with `α`. -/
theorem map_compareSnd_commSqEquiv
    (x : BalancedExtension π₁ (BalancedExtension p₁ (PatchedModule h α))) :
    BalancedExtension.map π₂ (compareSnd h α) (commSqEquiv h _ x) =
      α (BalancedExtension.map π₁ (compareFst h α) x) := by
  induction x using BalancedExtension.induction_on with
  | tmul t z =>
    induction z using BalancedExtension.induction_on with
    | tmul s m =>
      -- `t ⊗ (s • m.fst) = (t * π₁ s) • (1 ⊗ m.fst)`, which `α` sends to
      -- `(t * π₁ s) • (1 ⊗ m.snd) = t ⊗ (s • m.snd)`.
      simp only [commSqEquiv_tmul, map_tmul, compareSnd_tmul, compareFst_tmul, one_smul,
        tmul_smul]
      rw [tmul_eq_smul_one_tmul (f := π₁), map_smul, apply_one_tmul_fst]
      simp
    | add z z' hz hz' => simp only [tmul_add, _root_.map_add, hz, hz']
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

variable {P₁' P₂' : Type*} [AddCommGroup P₁'] [Module A₁ P₁'] [AddCommGroup P₂'] [Module A₂ P₂']
  {α' : BalancedExtension π₁ P₁' →ₗ[Q] BalancedExtension π₂ P₂'}

/-- The first comparison map is natural in morphisms of patching triples. -/
@[simp]
theorem compareFst_map_map (g₁ : P₁ →ₗ[A₁] P₁') (g₂ : P₂ →ₗ[A₂] P₂')
    (hg : ∀ x, α' (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x))
    (x : BalancedExtension p₁ (PatchedModule h α)) :
    compareFst h α' (BalancedExtension.map p₁ (PatchedModule.map g₁ g₂ hg) x) =
      g₁ (compareFst h α x) :=
  LinearMap.congr_fun (BalancedExtension.hom_ext fun m ↦ by simp : compareFst h α' ∘ₗ
    BalancedExtension.map p₁ (PatchedModule.map g₁ g₂ hg) = g₁ ∘ₗ compareFst h α) x

/-- The second comparison map is natural in morphisms of patching triples. -/
@[simp]
theorem compareSnd_map_map (g₁ : P₁ →ₗ[A₁] P₁') (g₂ : P₂ →ₗ[A₂] P₂')
    (hg : ∀ x, α' (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x))
    (x : BalancedExtension p₂ (PatchedModule h α)) :
    compareSnd h α' (BalancedExtension.map p₂ (PatchedModule.map g₁ g₂ hg) x) =
      g₂ (compareSnd h α x) :=
  LinearMap.congr_fun (BalancedExtension.hom_ext fun m ↦ by simp : compareSnd h α' ∘ₗ
    BalancedExtension.map p₂ (PatchedModule.map g₁ g₂ hg) = g₂ ∘ₗ compareSnd h α) x

end Compare

section Triple

variable (h : π₁.comp p₁ = π₂.comp p₂) {P : Type*} [AddCommGroup P] [Module D P]

/-- On the patching triple of a `D`-module `P`, the first comparison map undoes the extension of
`p ↦ (1 ⊗ p, 1 ⊗ p)`. -/
@[simp]
theorem compareFst_map_toPatchedModule (x : BalancedExtension p₁ P) :
    compareFst h _ (BalancedExtension.map p₁ (toPatchedModule h P) x) = x :=
  LinearMap.congr_fun (BalancedExtension.hom_ext fun m ↦ by simp : compareFst h _ ∘ₗ
    BalancedExtension.map p₁ (toPatchedModule h P) = LinearMap.id) x

/-- On the patching triple of a `D`-module `P`, the second comparison map undoes the extension of
`p ↦ (1 ⊗ p, 1 ⊗ p)`. -/
@[simp]
theorem compareSnd_map_toPatchedModule (x : BalancedExtension p₂ P) :
    compareSnd h _ (BalancedExtension.map p₂ (toPatchedModule h P) x) = x :=
  LinearMap.congr_fun (BalancedExtension.hom_ext fun m ↦ by simp : compareSnd h _ ∘ₗ
    BalancedExtension.map p₂ (toPatchedModule h P) = LinearMap.id) x

end Triple

end PatchedModule

open PatchedModule

section Retract

variable {P₁ P₂ : Type*} [AddCommGroup P₁] [Module A₁ P₁] [AddCommGroup P₂] [Module A₂ P₂]
  (h : π₁.comp p₁ = π₂.comp p₂)

/-- The conclusions of Milnor's patching theorem for one triple: its patched module is finitely
generated projective and both comparison maps are bijective. -/
private structure IsPatched (α : BalancedExtension π₁ P₁ →ₗ[Q] BalancedExtension π₂ P₂) :
    Prop where
  finite : Module.Finite D (PatchedModule h α)
  projective : Module.Projective D (PatchedModule h α)
  bijective_fst : Function.Bijective (compareFst h α)
  bijective_snd : Function.Bijective (compareSnd h α)

/-- The conclusions of Milnor's patching theorem pass to retracts of patching triples. -/
private theorem IsPatched.of_retract {α : BalancedExtension π₁ P₁ →ₗ[Q] BalancedExtension π₂ P₂}
    {E₁ E₂ : Type*} [AddCommGroup E₁] [Module A₁ E₁] [AddCommGroup E₂] [Module A₂ E₂]
    {β : BalancedExtension π₁ E₁ →ₗ[Q] BalancedExtension π₂ E₂} (g₁ : P₁ →ₗ[A₁] E₁)
    (g₂ : P₂ →ₗ[A₂] E₂) (r₁ : E₁ →ₗ[A₁] P₁) (r₂ : E₂ →ₗ[A₂] P₂)
    (hg : ∀ x, β (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x))
    (hr : ∀ x, α (BalancedExtension.map π₁ r₁ x) = BalancedExtension.map π₂ r₂ (β x))
    (hrg₁ : r₁ ∘ₗ g₁ = LinearMap.id) (hrg₂ : r₂ ∘ₗ g₂ = LinearMap.id) (hβ : IsPatched h β) :
    IsPatched h α := by
  have := hβ.finite
  have := hβ.projective
  set i := PatchedModule.map (h := h) g₁ g₂ hg
  set r := PatchedModule.map (h := h) r₁ r₂ hr
  have hri : r ∘ₗ i = LinearMap.id := LinearMap.ext fun m ↦ PatchedModule.ext
    (by simpa [i, r] using LinearMap.congr_fun hrg₁ m.fst)
    (by simpa [i, r] using LinearMap.congr_fun hrg₂ m.snd)
  refine ⟨.of_surjective r fun x ↦ ⟨i x, LinearMap.congr_fun hri x⟩, .of_split i r hri, ?_, ?_⟩
  · exact Function.bijective_of_retract hβ.bijective_fst (compareFst_map_map h α g₁ g₂ hg)
      (compareFst_map_map h β r₁ r₂ hr) (map_map_of_comp_eq_id hri) (LinearMap.congr_fun hrg₁)
  · exact Function.bijective_of_retract hβ.bijective_snd (compareSnd_map_map h α g₁ g₂ hg)
      (compareSnd_map_map h β r₁ r₂ hr) (map_map_of_comp_eq_id hri) (LinearMap.congr_fun hrg₂)

variable (hD : ∀ a₁ a₂, π₁ a₁ = π₂ a₂ → ∃! d, p₁ d = a₁ ∧ p₂ d = a₂)

include hD in
/-- Over a fibre-product square, Milnor's patching theorem holds for the patching triple of a
finitely generated projective `D`-module. -/
private theorem isPatched_commSqEquiv (F : Type*) [AddCommGroup F] [Module D F] [Module.Finite D F]
    [Module.Projective D F] : IsPatched h (commSqEquiv h F).toLinearMap := by
  have hF := bijective_toPatchedModule h hD F
  have hs₁ := BalancedExtension.map_surjective (f := p₁) hF.2
  have hs₂ := BalancedExtension.map_surjective (f := p₂) hF.2
  refine ⟨.equiv (patchedModuleEquiv h hD F), .of_equiv (patchedModuleEquiv h hD F),
    ⟨fun x x' hxx' ↦ ?_, fun x ↦ ⟨_, compareFst_map_toPatchedModule h x⟩⟩,
    ⟨fun x x' hxx' ↦ ?_, fun x ↦ ⟨_, compareSnd_map_toPatchedModule h x⟩⟩⟩
  · obtain ⟨x, rfl⟩ := hs₁ x
    obtain ⟨x', rfl⟩ := hs₁ x'
    simp only [compareFst_map_toPatchedModule] at hxx'
    rw [hxx']
  · obtain ⟨x, rfl⟩ := hs₂ x
    obtain ⟨x', rfl⟩ := hs₂ x'
    simp only [compareSnd_map_toPatchedModule] at hxx'
    rw [hxx']

end Retract

section Whitehead

/-! ### Embedding a triple into the triple of a free module

Fix retractions `P₁ → A₁ ⊗_D G₁ → P₁` and `P₂ → A₂ ⊗_D G₂ → P₂` and lifts `x`, `y` of the two maps
between `Q ⊗ G₁` and `Q ⊗ G₂` obtained from `α` and its inverse. The automorphism
`(1 + X) (1 + Y) (1 + X)` of `A₁ ⊗_D (G₁ × G₂)` built from the block unipotents `X` and `Y` then
makes `(P₁, P₂, α)` a retract of the patching triple of `G₁ × G₂`. -/

variable {G₁ G₂ : Type*} [AddCommGroup G₁] [Module D G₁] [AddCommGroup G₂] [Module D G₂]

/-- The block unipotent endomorphism `(u, v) ↦ (u + x v, v)` of `A₁ ⊗_D (G₁ × G₂)`, minus the
identity. -/
private def upperBlock (x : BalancedExtension p₁ G₂ →ₗ[A₁] BalancedExtension p₁ G₁) :
    Module.End A₁ (BalancedExtension p₁ (G₁ × G₂)) :=
  BalancedExtension.map p₁ (LinearMap.inl D G₁ G₂) ∘ₗ x ∘ₗ
    BalancedExtension.map p₁ (LinearMap.snd D G₁ G₂)

/-- The block unipotent endomorphism `(u, v) ↦ (u, v + y u)` of `A₁ ⊗_D (G₁ × G₂)`, minus the
identity. -/
private def lowerBlock (y : BalancedExtension p₁ G₁ →ₗ[A₁] BalancedExtension p₁ G₂) :
    Module.End A₁ (BalancedExtension p₁ (G₁ × G₂)) :=
  BalancedExtension.map p₁ (LinearMap.inr D G₁ G₂) ∘ₗ y ∘ₗ
    BalancedExtension.map p₁ (LinearMap.fst D G₁ G₂)

private theorem upperBlock_mul_self (x : BalancedExtension p₁ G₂ →ₗ[A₁] BalancedExtension p₁ G₁) :
    upperBlock x * upperBlock x = 0 :=
  LinearMap.ext fun w ↦ by simp [upperBlock]

private theorem lowerBlock_mul_self (y : BalancedExtension p₁ G₁ →ₗ[A₁] BalancedExtension p₁ G₂) :
    lowerBlock y * lowerBlock y = 0 :=
  LinearMap.ext fun w ↦ by simp [lowerBlock]

variable (x : BalancedExtension p₁ G₂ →ₗ[A₁] BalancedExtension p₁ G₁)
  (y : BalancedExtension p₁ G₁ →ₗ[A₁] BalancedExtension p₁ G₂)

/-- The automorphism `(1 + X) (1 + Y) (1 + X)` of `A₁ ⊗_D (G₁ × G₂)`. -/
private def whiteheadAut : Module.End A₁ (BalancedExtension p₁ (G₁ × G₂)) :=
  (1 + upperBlock x) * (1 + lowerBlock y) * (1 + upperBlock x)

/-- The inverse `(1 - X) (1 - Y) (1 - X)` of `whiteheadAut x y`. -/
private def whiteheadAutInv : Module.End A₁ (BalancedExtension p₁ (G₁ × G₂)) :=
  (1 - upperBlock x) * (1 - lowerBlock y) * (1 - upperBlock x)

private theorem whiteheadAutInv_mul_whiteheadAut : whiteheadAutInv x y * whiteheadAut x y = 1 := by
  have hX := one_sub_mul_one_add_of_mul_self_eq_zero (upperBlock_mul_self x)
  simp only [whiteheadAutInv, whiteheadAut, mul_assoc]
  -- Cancel the middle pair `(1 - X) (1 + X)`, then `(1 - Y) (1 + Y)`, then the outer pair.
  rw [← mul_assoc (1 - upperBlock x) (1 + upperBlock x), hX, one_mul,
    ← mul_assoc (1 - lowerBlock y),
    one_sub_mul_one_add_of_mul_self_eq_zero (lowerBlock_mul_self y), one_mul, hX]

private theorem whiteheadAut_mul_whiteheadAutInv : whiteheadAut x y * whiteheadAutInv x y = 1 := by
  have hX := one_add_mul_one_sub_of_mul_self_eq_zero (upperBlock_mul_self x)
  simp only [whiteheadAutInv, whiteheadAut, mul_assoc]
  -- Cancel the middle pair `(1 + X) (1 - X)`, then `(1 + Y) (1 - Y)`, then the outer pair.
  rw [← mul_assoc (1 + upperBlock x) (1 - upperBlock x), hX, one_mul,
    ← mul_assoc (1 + lowerBlock y),
    one_add_mul_one_sub_of_mul_self_eq_zero (lowerBlock_mul_self y), one_mul, hX]

/-- `(1 + X) (1 + Y) (1 + X) (u, 0) = (u + x (y u), y u)`. -/
private theorem whiteheadAut_comp_inl :
    whiteheadAut x y ∘ₗ BalancedExtension.map p₁ (LinearMap.inl D G₁ G₂) =
      BalancedExtension.map p₁ (LinearMap.inl D G₁ G₂) ∘ₗ (LinearMap.id + x ∘ₗ y) +
        BalancedExtension.map p₁ (LinearMap.inr D G₁ G₂) ∘ₗ y := by
  ext v
  simp only [whiteheadAut, upperBlock, lowerBlock, LinearMap.comp_apply, mul_apply_eq_comp,
    LinearMap.add_apply, one_apply_eq_self, LinearMap.id_apply, _root_.map_add, map_fst_map_inl,
    map_snd_map_inl, map_snd_map_inr, _root_.map_zero, add_zero]
  abel

/-- The second component of `(1 + X) (1 + Y) (1 + X) (u, v)` is `v + y u + y (x v)`. -/
private theorem snd_comp_whiteheadAut :
    BalancedExtension.map p₁ (LinearMap.snd D G₁ G₂) ∘ₗ whiteheadAut x y =
      BalancedExtension.map p₁ (LinearMap.snd D G₁ G₂) +
        y ∘ₗ BalancedExtension.map p₁ (LinearMap.fst D G₁ G₂) +
          y ∘ₗ x ∘ₗ BalancedExtension.map p₁ (LinearMap.snd D G₁ G₂) := by
  ext w
  simp only [whiteheadAut, upperBlock, lowerBlock, LinearMap.comp_apply, mul_apply_eq_comp,
    LinearMap.add_apply, one_apply_eq_self, _root_.map_add, map_fst_map_inl, map_snd_map_inl,
    map_snd_map_inr, _root_.map_zero, add_zero, zero_add]

variable {P₁ P₂ : Type*} [AddCommGroup P₁] [Module A₁ P₁] [AddCommGroup P₂] [Module A₂ P₂]
  (h : π₁.comp p₁ = π₂.comp p₂) (α : BalancedExtension π₁ P₁ ≃ₗ[Q] BalancedExtension π₂ P₂)
  {i₁ : P₁ →ₗ[A₁] BalancedExtension p₁ G₁} {r₁ : BalancedExtension p₁ G₁ →ₗ[A₁] P₁}
  {i₂ : P₂ →ₗ[A₂] BalancedExtension p₂ G₂} {r₂ : BalancedExtension p₂ G₂ →ₗ[A₂] P₂}
  {x y}

/-- The embedding of `P₁` into `A₁ ⊗_D (G₁ × G₂)` along `whiteheadAut x y` is compatible with the
embedding of `P₂` into the second factor of `A₂ ⊗_D (G₁ × G₂)`. -/
private theorem commSqEquiv_map_whiteheadAut_inl (hri₁ : r₁ ∘ₗ i₁ = LinearMap.id)
    (hri₂ : r₂ ∘ₗ i₂ = LinearMap.id)
    (hx : ∀ w, BalancedExtension.map π₁ x w = -BalancedExtension.map π₁ i₁
      (α.symm (BalancedExtension.map π₂ r₂ (commSqEquiv h G₂ w))))
    (hy : ∀ w, BalancedExtension.map π₁ y w = (commSqEquiv h G₂).symm
      (BalancedExtension.map π₂ i₂ (α (BalancedExtension.map π₁ r₁ w))))
    (z : BalancedExtension π₁ P₁) :
    commSqEquiv h (G₁ × G₂) (BalancedExtension.map π₁
        (whiteheadAut x y ∘ₗ BalancedExtension.map p₁ (LinearMap.inl D G₁ G₂) ∘ₗ i₁) z) =
      BalancedExtension.map π₂ (BalancedExtension.map p₂ (LinearMap.inr D G₁ G₂) ∘ₗ i₂) (α z) := by
  rw [← LinearMap.comp_assoc, whiteheadAut_comp_inl]
  simp only [BalancedExtension.map_comp, BalancedExtension.map_add, BalancedExtension.map_id,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, hx, hy,
    LinearEquiv.apply_symm_apply, map_map_of_comp_eq_id hri₁, map_map_of_comp_eq_id hri₂,
    LinearEquiv.symm_apply_apply, add_neg_cancel, _root_.map_zero, zero_add, commSqEquiv_map]

/-- Projecting `A₂ ⊗_D (G₁ × G₂)` onto `P₂` after `whiteheadAut x y` is compatible with
projecting `A₁ ⊗_D (G₁ × G₂)` onto `P₁`. -/
private theorem map_snd_commSqEquiv_map_whiteheadAut (hri₁ : r₁ ∘ₗ i₁ = LinearMap.id)
    (hri₂ : r₂ ∘ₗ i₂ = LinearMap.id)
    (hx : ∀ w, BalancedExtension.map π₁ x w = -BalancedExtension.map π₁ i₁
      (α.symm (BalancedExtension.map π₂ r₂ (commSqEquiv h G₂ w))))
    (hy : ∀ w, BalancedExtension.map π₁ y w = (commSqEquiv h G₂).symm
      (BalancedExtension.map π₂ i₂ (α (BalancedExtension.map π₁ r₁ w))))
    (w : BalancedExtension π₁ (BalancedExtension p₁ (G₁ × G₂))) :
    BalancedExtension.map π₂ (r₂ ∘ₗ BalancedExtension.map p₂ (LinearMap.snd D G₁ G₂))
        (commSqEquiv h (G₁ × G₂) (BalancedExtension.map π₁ (whiteheadAut x y) w)) =
      α (BalancedExtension.map π₁ (r₁ ∘ₗ BalancedExtension.map p₁ (LinearMap.fst D G₁ G₂)) w) := by
  rw [BalancedExtension.map_comp, LinearMap.comp_apply, ← commSqEquiv_map, ← LinearMap.comp_apply,
    ← BalancedExtension.map_comp, snd_comp_whiteheadAut]
  simp only [BalancedExtension.map_comp, BalancedExtension.map_add, LinearMap.comp_apply,
    LinearMap.add_apply, hx, hy, LinearEquiv.apply_symm_apply, map_map_of_comp_eq_id hri₁,
    map_map_of_comp_eq_id hri₂, _root_.map_add, _root_.map_neg]
  abel

/-- Milnor's patching theorem for one triple when `π₁` is surjective, given retractions
`P₁ → A₁ ⊗_D G₁ → P₁` and `P₂ → A₂ ⊗_D G₂ → P₂` onto extensions of finitely generated
projective `D`-modules: `(P₁, P₂, α)` is a retract of the patching triple of `G₁ × G₂`. -/
private theorem isPatched_of_retraction
    (hD : ∀ a₁ a₂, π₁ a₁ = π₂ a₂ → ∃! d, p₁ d = a₁ ∧ p₂ d = a₂)
    (hπ : Function.Surjective π₁) [Module.Finite D G₁]
    [Module.Projective D G₁] [Module.Finite D G₂] [Module.Projective D G₂]
    (hri₁ : r₁ ∘ₗ i₁ = LinearMap.id) (hri₂ : r₂ ∘ₗ i₂ = LinearMap.id) :
    IsPatched h α.toLinearMap := by
  obtain ⟨x, hx⟩ := exists_map_eq_of_surjective hπ (-(BalancedExtension.map π₁ i₁ ∘ₗ
    α.symm.toLinearMap ∘ₗ BalancedExtension.map π₂ r₂ ∘ₗ (commSqEquiv h G₂).toLinearMap))
  obtain ⟨y, hy⟩ := exists_map_eq_of_surjective hπ ((commSqEquiv h G₂).symm.toLinearMap ∘ₗ
    BalancedExtension.map π₂ i₂ ∘ₗ α.toLinearMap ∘ₗ BalancedExtension.map π₁ r₁)
  have hx' (w : _) := LinearMap.congr_fun hx w
  have hy' (w : _) := LinearMap.congr_fun hy w
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hx' hy'
  have hψφ (u : _) : whiteheadAutInv x y (whiteheadAut x y u) = u := by
    rw [← mul_apply_eq_comp, whiteheadAutInv_mul_whiteheadAut, one_apply_eq_self]
  have hφψ : whiteheadAut x y ∘ₗ whiteheadAutInv x y = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, whiteheadAut_mul_whiteheadAutInv, Module.End.one_eq_id]
  refine IsPatched.of_retract h
    (whiteheadAut x y ∘ₗ BalancedExtension.map p₁ (LinearMap.inl D G₁ G₂) ∘ₗ i₁)
    (BalancedExtension.map p₂ (LinearMap.inr D G₁ G₂) ∘ₗ i₂)
    (r₁ ∘ₗ BalancedExtension.map p₁ (LinearMap.fst D G₁ G₂) ∘ₗ whiteheadAutInv x y)
    (r₂ ∘ₗ BalancedExtension.map p₂ (LinearMap.snd D G₁ G₂))
    (commSqEquiv_map_whiteheadAut_inl h α hri₁ hri₂ hx' hy') (fun w ↦ ?_) ?_ ?_
    (isPatched_commSqEquiv h hD (G₁ × G₂))
  · have := map_snd_commSqEquiv_map_whiteheadAut h α hri₁ hri₂ hx' hy'
      (BalancedExtension.map π₁ (whiteheadAutInv x y) w)
    rw [map_map_of_comp_eq_id hφψ] at this
    simpa only [BalancedExtension.map_comp, LinearMap.comp_apply, LinearEquiv.coe_coe] using
      this.symm
  · ext z
    simpa [hψφ] using LinearMap.congr_fun hri₁ z
  · ext z
    simpa using LinearMap.congr_fun hri₂ z

end Whitehead

section Patching

variable {P₁ P₂ : Type*} [AddCommGroup P₁] [Module A₁ P₁] [AddCommGroup P₂] [Module A₂ P₂]
  (h : π₁.comp p₁ = π₂.comp p₂) (α : BalancedExtension π₁ P₁ ≃ₗ[Q] BalancedExtension π₂ P₂)

/-- Exchanging the two sides of the square identifies the patched module of `(P₁, P₂, α)` with
that of `(P₂, P₁, α⁻¹)`. -/
private def swapEquiv :
    PatchedModule h α.toLinearMap ≃ₗ[D] PatchedModule h.symm α.symm.toLinearMap where
  toFun m := ⟨m.snd, m.fst, α.symm_apply_eq.2 m.apply_one_tmul_fst.symm⟩
  invFun m := ⟨m.snd, m.fst, (α.symm_apply_eq.1 m.apply_one_tmul_fst).symm⟩
  map_add' _ _ := PatchedModule.ext (by simp) (by simp)
  map_smul' _ _ := PatchedModule.ext (by simp) (by simp)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
private theorem fst_swapEquiv (m : PatchedModule h α.toLinearMap) :
    (swapEquiv h α m).fst = m.snd := (rfl)

@[simp]
private theorem snd_swapEquiv (m : PatchedModule h α.toLinearMap) :
    (swapEquiv h α m).snd = m.fst := (rfl)

/-- Milnor's patching theorem for `(P₁, P₂, α)` follows from that for `(P₂, P₁, α⁻¹)` over the
square with its two sides exchanged. -/
private theorem IsPatched.of_swap (hα : IsPatched h.symm α.symm.toLinearMap) :
    IsPatched h α.toLinearMap := by
  have := hα.finite
  have := hα.projective
  have h₁ : compareFst h α.toLinearMap = compareSnd h.symm α.symm.toLinearMap ∘ₗ
      (BalancedExtension.congr p₁ (swapEquiv h α)).toLinearMap :=
    BalancedExtension.hom_ext fun m ↦ by simp
  have h₂ : compareSnd h α.toLinearMap = compareFst h.symm α.symm.toLinearMap ∘ₗ
      (BalancedExtension.congr p₂ (swapEquiv h α)).toLinearMap :=
    BalancedExtension.hom_ext fun m ↦ by simp
  refine ⟨.equiv (swapEquiv h α).symm, .of_equiv (swapEquiv h α).symm, ?_, ?_⟩
  · rw [h₁, LinearMap.coe_comp]
    exact hα.bijective_snd.comp (LinearEquiv.bijective _)
  · rw [h₂, LinearMap.coe_comp]
    exact hα.bijective_fst.comp (LinearEquiv.bijective _)

variable (hD : ∀ a₁ a₂, π₁ a₁ = π₂ a₂ → ∃! d, p₁ d = a₁ ∧ p₂ d = a₂)
  (hπ : Function.Surjective π₁ ∨ Function.Surjective π₂)
  [Module.Finite A₁ P₁] [Module.Projective A₁ P₁] [Module.Finite A₂ P₂] [Module.Projective A₂ P₂]

include hD in
/-- Milnor's patching theorem for one triple, when `π₁` is surjective. -/
private theorem isPatched_of_surjective_left (hπ : Function.Surjective π₁) :
    IsPatched h α.toLinearMap := by
  obtain ⟨n, f₁, g₁, -, -, hfg₁⟩ := Module.Finite.exists_comp_eq_id_of_projective A₁ P₁
  obtain ⟨m, f₂, g₂, -, -, hfg₂⟩ := Module.Finite.exists_comp_eq_id_of_projective A₂ P₂
  refine isPatched_of_retraction h α hD (i₁ := (piScalarRight p₁ (Fin n)).symm.toLinearMap ∘ₗ g₁)
    (r₁ := f₁ ∘ₗ (piScalarRight p₁ (Fin n)).toLinearMap)
    (i₂ := (piScalarRight p₂ (Fin m)).symm.toLinearMap ∘ₗ g₂)
    (r₂ := f₂ ∘ₗ (piScalarRight p₂ (Fin m)).toLinearMap) hπ ?_ ?_
  · ext z
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      LinearMap.congr_fun hfg₁ z
  · ext z
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      LinearMap.congr_fun hfg₂ z

include hD hπ in
/-- **Milnor's patching theorem**, for one triple. -/
private theorem isPatched : IsPatched h α.toLinearMap := by
  rcases hπ with hπ | hπ
  · exact isPatched_of_surjective_left h α hD hπ
  · refine IsPatched.of_swap h α (isPatched_of_surjective_left h.symm α.symm
      (fun a₂ a₁ ha ↦ ?_) hπ)
    obtain ⟨d, hd, hu⟩ := hD a₁ a₂ ha.symm
    exact ⟨d, hd.symm, fun d' hd' ↦ hu d' hd'.symm⟩

include hD hπ in
/-- **Milnor patching: patched modules are finitely generated.** Over a fibre-product square with
a surjective leg, the patched module of finitely generated projective modules `P₁`, `P₂` glued
along an isomorphism `α` is finitely generated. -/
theorem finite_patchedModule : Module.Finite D (PatchedModule h α.toLinearMap) :=
  (isPatched h α hD hπ).finite

include hD hπ in
/-- **Milnor patching: patched modules are projective.** Over a fibre-product square with a
surjective leg, the patched module of finitely generated projective modules `P₁`, `P₂` glued
along an isomorphism `α` is projective. -/
theorem projective_patchedModule : Module.Projective D (PatchedModule h α.toLinearMap) :=
  (isPatched h α hD hπ).projective

namespace PatchedModule

include hD hπ in
/-- **Milnor patching: base change recovers `P₁`.** Over a fibre-product square with a surjective
leg, for finitely generated projective `P₁`, `P₂` and an isomorphism `α`, the comparison map
`A₁ ⊗_D M(P₁, P₂, α) → P₁` is bijective. -/
theorem bijective_compareFst : Function.Bijective (compareFst h α.toLinearMap) :=
  (isPatched h α hD hπ).bijective_fst

include hD hπ in
/-- **Milnor patching: base change recovers `P₂`.** Over a fibre-product square with a surjective
leg, for finitely generated projective `P₁`, `P₂` and an isomorphism `α`, the comparison map
`A₂ ⊗_D M(P₁, P₂, α) → P₂` is bijective. -/
theorem bijective_compareSnd : Function.Bijective (compareSnd h α.toLinearMap) :=
  (isPatched h α hD hπ).bijective_snd

/-- The comparison isomorphism `A₁ ⊗_D M(P₁, P₂, α) ≃ P₁`, `s ⊗ (x, y) ↦ s • x`, over a
fibre-product square with a surjective leg, for finitely generated projective `P₁`, `P₂`. -/
noncomputable def compareFstEquiv :
    BalancedExtension p₁ (PatchedModule h α.toLinearMap) ≃ₗ[A₁] P₁ :=
  .ofBijective _ (bijective_compareFst h α hD hπ)

/-- The comparison isomorphism `A₂ ⊗_D M(P₁, P₂, α) ≃ P₂`, `s ⊗ (x, y) ↦ s • y`, over a
fibre-product square with a surjective leg, for finitely generated projective `P₁`, `P₂`. -/
noncomputable def compareSndEquiv :
    BalancedExtension p₂ (PatchedModule h α.toLinearMap) ≃ₗ[A₂] P₂ :=
  .ofBijective _ (bijective_compareSnd h α hD hπ)

@[simp]
theorem compareFstEquiv_apply (x : BalancedExtension p₁ (PatchedModule h α.toLinearMap)) :
    compareFstEquiv h α hD hπ x = compareFst h α.toLinearMap x := (rfl)

@[simp]
theorem compareSndEquiv_apply (x : BalancedExtension p₂ (PatchedModule h α.toLinearMap)) :
    compareSndEquiv h α hD hπ x = compareSnd h α.toLinearMap x := (rfl)

/-- The inverse of `compareFstEquiv` sends the first component of `m ∈ M(P₁, P₂, α)` to
`1 ⊗ m`. -/
@[simp]
theorem compareFstEquiv_symm_fst (m : PatchedModule h α.toLinearMap) :
    (compareFstEquiv h α hD hπ).symm m.fst = tmul p₁ 1 m :=
  (LinearEquiv.symm_apply_eq _).2 (by simp)

/-- The inverse of `compareSndEquiv` sends the second component of `m ∈ M(P₁, P₂, α)` to
`1 ⊗ m`. -/
@[simp]
theorem compareSndEquiv_symm_snd (m : PatchedModule h α.toLinearMap) :
    (compareSndEquiv h α hD hπ).symm m.snd = tmul p₂ 1 m :=
  (LinearEquiv.symm_apply_eq _).2 (by simp)

end PatchedModule

end Patching

end TauCeti
