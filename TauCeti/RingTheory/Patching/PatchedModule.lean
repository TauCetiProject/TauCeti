/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.LocalRing.Pullback
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension

/-!
# Patched modules over a commutative square of rings

Consider a commutative square of possibly noncommutative rings

```text
  D ──p₂──→ A₂
  │          │
  p₁         π₂
  ↓          ↓
  A₁ ──π₁──→ Q
```

with `π₁ ∘ p₁ = π₂ ∘ p₂`. A *patching triple* consists of a left `A₁`-module `P₁`, a left
`A₂`-module `P₂` and a `Q`-linear map `α : Q ⊗_{A₁} P₁ → Q ⊗_{A₂} P₂`. Its **patched module** is

  `M(P₁, P₂, α) = {(x, y) ∈ P₁ × P₂ | α (1 ⊗ x) = 1 ⊗ y}`,

a left `D`-module through `d · (x, y) = (p₁ d · x, p₂ d · y)`. Extension of scalars is
`TauCeti.BalancedExtension`, so no commutativity is assumed.

Every left `D`-module `P` gives a patching triple `(A₁ ⊗_D P, A₂ ⊗_D P, α_P)`, where the gluing
isomorphism `α_P : Q ⊗_{A₁} (A₁ ⊗_D P) ≃ Q ⊗_{A₂} (A₂ ⊗_D P)` is the composite of the two
identifications with `Q ⊗_D P` along the two sides of the square, and `p ↦ (1 ⊗ p, 1 ⊗ p)` maps `P`
into the patched module of its triple. When the square is a fibre product, that is when every pair
`(a₁, a₂)` with `π₁ a₁ = π₂ a₂` comes from exactly one `d ∈ D`, this map is an isomorphism for
every finitely generated projective `P`; for `P = D` it is the fibre-product property itself.
Consequently a `D`-linear map into a finitely generated projective module is the same as a
compatible pair of maps between the extensions to `A₁` and `A₂`: extension of scalars from `D` to
patching triples is fully faithful on finitely generated projective modules. No leg of the square
needs to be surjective for these statements. Surjectivity of a leg is needed for the converse
direction of Milnor's patching theorem, that every patching triple of finitely generated
projective modules arises in this way, which is not proved here.

The canonical fibre product of rings is Mathlib's `RingHom.pullback π₁ π₂`, which satisfies the
fibre-product hypothesis (`RingHom.existsUnique_pullbackFst_eq_and_pullbackSnd_eq`). The statements
are about left modules over an arbitrary commutative square, rather than over `RingHom.pullback`
only, so that they also apply to right modules over a fibre product, as left modules over the
square of opposite rings.

## Main definitions

* `TauCeti.PatchedModule h α`: the patched module of a triple `(P₁, P₂, α)` over a commutative
  square `h : π₁.comp p₁ = π₂.comp p₂`, with its semilinear projections
  `TauCeti.PatchedModule.fstHom` and `TauCeti.PatchedModule.sndHom`.
* `TauCeti.PatchedModule.lift`: the universal property of the patched module.
* `TauCeti.PatchedModule.map`: the `D`-linear map induced by a morphism of patching triples.
* `TauCeti.BalancedExtension.commSqEquiv h P`: the gluing isomorphism
  `Q ⊗_{A₁} (A₁ ⊗_D P) ≃ Q ⊗_{A₂} (A₂ ⊗_D P)`, `t ⊗ (s ⊗ p) ↦ (t * π₁ s) ⊗ (1 ⊗ p)`, with
  inverse `t ⊗ (s ⊗ p) ↦ (t * π₂ s) ⊗ (1 ⊗ p)`.
* `TauCeti.toPatchedModule h P`: the `D`-linear map `p ↦ (1 ⊗ p, 1 ⊗ p)` from `P` to the patched
  module of its triple.
* `TauCeti.patchedModuleEquiv h hD P`: over a fibre-product square, the isomorphism of a finitely
  generated projective module with the patched module of its triple.

## Main results

* `TauCeti.bijective_toPatchedModule`: over a fibre-product square, a finitely generated
  projective module is the patched module of its triple.
* `TauCeti.BalancedExtension.existsUnique_map_eq_and_map_eq`: over a fibre-product square, a
  compatible pair of maps `A₁ ⊗_D P → A₁ ⊗_D P'`, `A₂ ⊗_D P → A₂ ⊗_D P'` comes from exactly one
  `D`-linear map `P → P'`, when `P'` is finitely generated projective.
* `RingHom.existsUnique_pullbackFst_eq_and_pullbackSnd_eq`: `RingHom.pullback π₁ π₂` is a fibre
  product in this sense, and `RingHom.existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq`: so is
  its opposite ring, over the square `RingHom.op_pullback_comm_sq` of opposite rings.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72, Princeton
  University Press (1971), §2 (the modules `M(P₁, P₂, h)` over a fibre product of rings, and the
  identification of a projective module with the patched module of its extensions).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, Theorem 2.7 (Milnor patching).
-/

public section

namespace TauCeti

open BalancedExtension

variable {D A₁ A₂ Q : Type*} [Ring D] [Ring A₁] [Ring A₂] [Ring Q]
  {p₁ : D →+* A₁} {p₂ : D →+* A₂} {π₁ : A₁ →+* Q} {π₂ : A₂ →+* Q}

section PatchedModule

variable {P₁ P₂ : Type*} [AddCommGroup P₁] [Module A₁ P₁] [AddCommGroup P₂] [Module A₂ P₂]

/-- The **patched module** `M(P₁, P₂, α) = {(x, y) ∈ P₁ × P₂ | α (1 ⊗ x) = 1 ⊗ y}` of a patching
triple over the commutative square `h : π₁ ∘ p₁ = π₂ ∘ p₂`. It is a left `D`-module through
`d · (x, y) = (p₁ d · x, p₂ d · y)`; the square `h` enters only through this action. -/
@[ext]
structure PatchedModule (_h : π₁.comp p₁ = π₂.comp p₂)
    (α : BalancedExtension π₁ P₁ →ₗ[Q] BalancedExtension π₂ P₂) where
  /-- The component in `P₁`. -/
  fst : P₁
  /-- The component in `P₂`. -/
  snd : P₂
  /-- The patching condition `α (1 ⊗ x) = 1 ⊗ y`. -/
  apply_one_tmul_fst : α (tmul π₁ 1 fst) = tmul π₂ 1 snd

namespace PatchedModule

variable {h : π₁.comp p₁ = π₂.comp p₂} {α : BalancedExtension π₁ P₁ →ₗ[Q] BalancedExtension π₂ P₂}

attribute [simp] apply_one_tmul_fst

instance : Zero (PatchedModule h α) where
  zero := ⟨0, 0, by simp⟩

instance : Add (PatchedModule h α) where
  add x y := ⟨x.fst + y.fst, x.snd + y.snd, by
    simp [tmul_add]⟩

instance : Neg (PatchedModule h α) where
  neg x := ⟨-x.fst, -x.snd, by simp⟩

instance : Sub (PatchedModule h α) where
  sub x y := ⟨x.fst - y.fst, x.snd - y.snd, by
    simp [tmul_sub]⟩

instance : SMul ℕ (PatchedModule h α) where
  smul n x := ⟨n • x.fst, n • x.snd, by
    rw [tmul_nsmul, tmul_nsmul, map_nsmul, x.apply_one_tmul_fst]⟩

instance : SMul ℤ (PatchedModule h α) where
  smul n x := ⟨n • x.fst, n • x.snd, by
    rw [tmul_zsmul, tmul_zsmul, map_zsmul, x.apply_one_tmul_fst]⟩

@[simp] theorem fst_zero : (0 : PatchedModule h α).fst = 0 := (rfl)
@[simp] theorem snd_zero : (0 : PatchedModule h α).snd = 0 := (rfl)
@[simp] theorem fst_add (x y : PatchedModule h α) : (x + y).fst = x.fst + y.fst := (rfl)
@[simp] theorem snd_add (x y : PatchedModule h α) : (x + y).snd = x.snd + y.snd := (rfl)
@[simp] theorem fst_neg (x : PatchedModule h α) : (-x).fst = -x.fst := (rfl)
@[simp] theorem snd_neg (x : PatchedModule h α) : (-x).snd = -x.snd := (rfl)
@[simp] theorem fst_sub (x y : PatchedModule h α) : (x - y).fst = x.fst - y.fst := (rfl)
@[simp] theorem snd_sub (x y : PatchedModule h α) : (x - y).snd = x.snd - y.snd := (rfl)
@[simp] theorem fst_nsmul (n : ℕ) (x : PatchedModule h α) : (n • x).fst = n • x.fst := (rfl)
@[simp] theorem snd_nsmul (n : ℕ) (x : PatchedModule h α) : (n • x).snd = n • x.snd := (rfl)
@[simp] theorem fst_zsmul (n : ℤ) (x : PatchedModule h α) : (n • x).fst = n • x.fst := (rfl)
@[simp] theorem snd_zsmul (n : ℤ) (x : PatchedModule h α) : (n • x).snd = n • x.snd := (rfl)

instance : AddCommGroup (PatchedModule h α) :=
  Function.Injective.addCommGroup (fun x ↦ (x.fst, x.snd))
    (fun _ _ hxy ↦ PatchedModule.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    (rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : SMul D (PatchedModule h α) where
  smul d x := ⟨p₁ d • x.fst, p₂ d • x.snd, by
    have hd : π₁ (p₁ d) = π₂ (p₂ d) := DFunLike.congr_fun h d
    simp only [one_tmul_smul, map_smul, x.apply_one_tmul_fst, hd]⟩

@[simp] theorem fst_smul (d : D) (x : PatchedModule h α) : (d • x).fst = p₁ d • x.fst := (rfl)
@[simp] theorem snd_smul (d : D) (x : PatchedModule h α) : (d • x).snd = p₂ d • x.snd := (rfl)

instance : Module D (PatchedModule h α) where
  one_smul x := PatchedModule.ext (by simp) (by simp)
  mul_smul d d' x := PatchedModule.ext (by simp [mul_smul]) (by simp [mul_smul])
  smul_zero d := PatchedModule.ext (by simp) (by simp)
  smul_add d x y := PatchedModule.ext (by simp) (by simp)
  add_smul d d' x := PatchedModule.ext (by simp [add_smul]) (by simp [add_smul])
  zero_smul x := PatchedModule.ext (by simp) (by simp)

variable (h α) in
/-- The first projection `M(P₁, P₂, α) → P₁`, semilinear along `p₁`. -/
def fstHom : PatchedModule h α →ₛₗ[p₁] P₁ where
  toFun := fst
  map_add' := fst_add
  map_smul' := fst_smul

variable (h α) in
/-- The second projection `M(P₁, P₂, α) → P₂`, semilinear along `p₂`. -/
def sndHom : PatchedModule h α →ₛₗ[p₂] P₂ where
  toFun := snd
  map_add' := snd_add
  map_smul' := snd_smul

@[simp] theorem fstHom_apply (x : PatchedModule h α) : fstHom h α x = x.fst := (rfl)
@[simp] theorem sndHom_apply (x : PatchedModule h α) : sndHom h α x = x.snd := (rfl)

section Lift

variable {N : Type*} [AddCommGroup N] [Module D N]

/-- **The universal property of the patched module.** A pair of maps `g₁ : N → P₁` and
`g₂ : N → P₂`, semilinear along `p₁` and `p₂`, with `α (1 ⊗ g₁ n) = 1 ⊗ g₂ n` for every `n`, is a
`D`-linear map `N → M(P₁, P₂, α)`. -/
def lift (g₁ : N →ₛₗ[p₁] P₁) (g₂ : N →ₛₗ[p₂] P₂)
    (hg : ∀ n, α (tmul π₁ 1 (g₁ n)) = tmul π₂ 1 (g₂ n)) : N →ₗ[D] PatchedModule h α where
  toFun n := ⟨g₁ n, g₂ n, hg n⟩
  map_add' n n' := PatchedModule.ext (by simp) (by simp)
  map_smul' d n := PatchedModule.ext (by simp) (by simp)

@[simp]
theorem fst_lift (g₁ : N →ₛₗ[p₁] P₁) (g₂ : N →ₛₗ[p₂] P₂)
    (hg : ∀ n, α (tmul π₁ 1 (g₁ n)) = tmul π₂ 1 (g₂ n)) (n : N) :
    (lift (h := h) g₁ g₂ hg n).fst = g₁ n := (rfl)

@[simp]
theorem snd_lift (g₁ : N →ₛₗ[p₁] P₁) (g₂ : N →ₛₗ[p₂] P₂)
    (hg : ∀ n, α (tmul π₁ 1 (g₁ n)) = tmul π₂ 1 (g₂ n)) (n : N) :
    (lift (h := h) g₁ g₂ hg n).snd = g₂ n := (rfl)

@[simp]
theorem fstHom_comp_lift (g₁ : N →ₛₗ[p₁] P₁) (g₂ : N →ₛₗ[p₂] P₂)
    (hg : ∀ n, α (tmul π₁ 1 (g₁ n)) = tmul π₂ 1 (g₂ n)) :
    (fstHom h α).comp (lift g₁ g₂ hg) = g₁ := (rfl)

@[simp]
theorem sndHom_comp_lift (g₁ : N →ₛₗ[p₁] P₁) (g₂ : N →ₛₗ[p₂] P₂)
    (hg : ∀ n, α (tmul π₁ 1 (g₁ n)) = tmul π₂ 1 (g₂ n)) :
    (sndHom h α).comp (lift g₁ g₂ hg) = g₂ := (rfl)

/-- `D`-linear maps into a patched module are determined by their two components: the uniqueness
half of the universal property `lift`. -/
@[ext]
theorem hom_ext {φ ψ : N →ₗ[D] PatchedModule h α}
    (h₁ : (fstHom h α).comp φ = (fstHom h α).comp ψ)
    (h₂ : (sndHom h α).comp φ = (sndHom h α).comp ψ) : φ = ψ :=
  LinearMap.ext fun n ↦ PatchedModule.ext (LinearMap.congr_fun h₁ n) (LinearMap.congr_fun h₂ n)

end Lift

section Map

variable {P₁' P₂' P₁'' P₂'' : Type*} [AddCommGroup P₁'] [Module A₁ P₁'] [AddCommGroup P₂']
  [Module A₂ P₂'] [AddCommGroup P₁''] [Module A₁ P₁''] [AddCommGroup P₂''] [Module A₂ P₂'']
  {α' : BalancedExtension π₁ P₁' →ₗ[Q] BalancedExtension π₂ P₂'}
  {α'' : BalancedExtension π₁ P₁'' →ₗ[Q] BalancedExtension π₂ P₂''}

/-- The `D`-linear map `M(P₁, P₂, α) → M(P₁', P₂', α')`, `(x, y) ↦ (g₁ x, g₂ y)`, induced by a
morphism of patching triples: linear maps `g₁ : P₁ → P₁'` and `g₂ : P₂ → P₂'` whose extensions to
`Q` intertwine `α` and `α'`. -/
def map (g₁ : P₁ →ₗ[A₁] P₁') (g₂ : P₂ →ₗ[A₂] P₂')
    (hg : ∀ x, α' (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x)) :
    PatchedModule h α →ₗ[D] PatchedModule h α' :=
  lift (g₁.comp (fstHom h α)) (g₂.comp (sndHom h α)) fun x ↦ by
    simpa using (hg (tmul π₁ 1 x.fst)).trans (congrArg _ x.apply_one_tmul_fst)

@[simp]
theorem fst_map (g₁ : P₁ →ₗ[A₁] P₁') (g₂ : P₂ →ₗ[A₂] P₂')
    (hg : ∀ x, α' (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x))
    (x : PatchedModule h α) : (map g₁ g₂ hg x).fst = g₁ x.fst := (rfl)

@[simp]
theorem snd_map (g₁ : P₁ →ₗ[A₁] P₁') (g₂ : P₂ →ₗ[A₂] P₂')
    (hg : ∀ x, α' (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x))
    (x : PatchedModule h α) : (map g₁ g₂ hg x).snd = g₂ x.snd := (rfl)

@[simp]
theorem map_id :
    map (h := h) (α := α) (α' := α) LinearMap.id LinearMap.id (fun x ↦ by simp) =
      LinearMap.id :=
  LinearMap.ext fun _ ↦ rfl

theorem map_comp (g₁ : P₁ →ₗ[A₁] P₁') (g₂ : P₂ →ₗ[A₂] P₂') (g₁' : P₁' →ₗ[A₁] P₁'')
    (g₂' : P₂' →ₗ[A₂] P₂'')
    (hg : ∀ x, α' (BalancedExtension.map π₁ g₁ x) = BalancedExtension.map π₂ g₂ (α x))
    (hg' : ∀ x, α'' (BalancedExtension.map π₁ g₁' x) = BalancedExtension.map π₂ g₂' (α' x)) :
    map (h := h) (g₁'.comp g₁) (g₂'.comp g₂)
        (fun x ↦ by simp only [BalancedExtension.map_comp, LinearMap.comp_apply, hg', hg]) =
      (map g₁' g₂' hg').comp (map g₁ g₂ hg) :=
  LinearMap.ext fun _ ↦ rfl

end Map

end PatchedModule

end PatchedModule

section Gluing

variable (h : π₁.comp p₁ = π₂.comp p₂) (P : Type*) [AddCommGroup P] [Module D P]
  {P' : Type*} [AddCommGroup P'] [Module D P']

/-- The **gluing isomorphism** of the patching triple of a left `D`-module `P` over the commutative
square `h : π₁ ∘ p₁ = π₂ ∘ p₂`: `Q ⊗_{A₁} (A₁ ⊗_D P) ≃ Q ⊗_D P ≃ Q ⊗_{A₂} (A₂ ⊗_D P)`, the
composite of the two cancellations of base change along the sides of the square. It sends
`t ⊗ (s ⊗ p)` to `(t * π₁ s) ⊗ (1 ⊗ p)` (`commSqEquiv_tmul`). -/
def BalancedExtension.commSqEquiv :
    BalancedExtension π₁ (BalancedExtension p₁ P) ≃ₗ[Q]
      BalancedExtension π₂ (BalancedExtension p₂ P) :=
  (cancelBaseChange p₁ π₁).trans ((congrRingHom h).trans (cancelBaseChange p₂ π₂).symm)

variable {P}

@[simp]
theorem BalancedExtension.commSqEquiv_tmul (t : Q) (s : A₁) (x : P) :
    commSqEquiv h P (tmul π₁ t (tmul p₁ s x)) = tmul π₂ (t * π₁ s) (tmul p₂ 1 x) := by
  simp [commSqEquiv]

@[simp]
theorem BalancedExtension.commSqEquiv_symm_tmul (t : Q) (s : A₂) (x : P) :
    (commSqEquiv h P).symm (tmul π₂ t (tmul p₂ s x)) = tmul π₁ (t * π₂ s) (tmul p₁ 1 x) := by
  simp [commSqEquiv]

/-- Cancelling base change after the gluing isomorphism is transport along the square. -/
@[simp]
theorem BalancedExtension.cancelBaseChange_commSqEquiv
    (x : BalancedExtension π₁ (BalancedExtension p₁ P)) :
    cancelBaseChange p₂ π₂ (commSqEquiv h P x) = congrRingHom h (cancelBaseChange p₁ π₁ x) := by
  simp [commSqEquiv]

/-- The gluing isomorphism is natural in the module. -/
theorem BalancedExtension.commSqEquiv_map (g : P →ₗ[D] P')
    (x : BalancedExtension π₁ (BalancedExtension p₁ P)) :
    commSqEquiv h P' (map π₁ (map p₁ g) x) = map π₂ (map p₂ g) (commSqEquiv h P x) := by
  induction x using induction_on with
  | tmul t z =>
    induction z using induction_on with
    | tmul s p => simp
    | add z z' hz hz' => simp only [tmul_add, _root_.map_add, hz, hz']
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

variable (P) in
/-- The `D`-linear map `p ↦ (1 ⊗ p, 1 ⊗ p)` from a left `D`-module `P` to the patched module of
its triple `(A₁ ⊗_D P, A₂ ⊗_D P, α_P)`, with `α_P` the gluing isomorphism `commSqEquiv h P`. -/
def toPatchedModule : P →ₗ[D] PatchedModule h (commSqEquiv h P).toLinearMap :=
  PatchedModule.lift (includeRight p₁ P) (includeRight p₂ P) fun x ↦ by simp

@[simp]
theorem PatchedModule.fst_toPatchedModule (x : P) :
    (toPatchedModule h P x).fst = tmul p₁ 1 x := by
  simp [toPatchedModule]

@[simp]
theorem PatchedModule.snd_toPatchedModule (x : P) :
    (toPatchedModule h P x).snd = tmul p₂ 1 x := by
  simp [toPatchedModule]

/-- `toPatchedModule` is natural: it intertwines a `D`-linear map `g : P → P'` with the map of
patched modules induced by the extensions of `g`. -/
@[simp]
theorem PatchedModule.map_toPatchedModule (g : P →ₗ[D] P') (x : P) :
    map (BalancedExtension.map p₁ g) (BalancedExtension.map p₂ g) (commSqEquiv_map h g)
        (toPatchedModule h P x) =
      toPatchedModule h P' (g x) :=
  PatchedModule.ext (by simp) (by simp)

end Gluing

section FibreProduct

variable (h : π₁.comp p₁ = π₂.comp p₂) (hD : ∀ a₁ a₂, π₁ a₁ = π₂ a₂ → ∃! d, p₁ d = a₁ ∧ p₂ d = a₂)

/-- On a finite free module the patching condition is the coordinatewise compatibility
`π₁ ∘ x = π₂ ∘ y` of the coordinate vectors `x` and `y`. -/
private theorem commSqEquiv_one_tmul_eq_iff (ι : Type*) [Fintype ι]
    (x : BalancedExtension p₁ (ι → D)) (y : BalancedExtension p₂ (ι → D)) :
    commSqEquiv h (ι → D) (tmul π₁ 1 x) = tmul π₂ 1 y ↔
      ∀ i, π₁ (piScalarRight p₁ ι x i) = π₂ (piScalarRight p₂ ι y i) := by
  rw [← (cancelBaseChange p₂ π₂).injective.eq_iff,
    ← (piScalarRight (π₂.comp p₂) ι).injective.eq_iff]
  simp [funext_iff]

include hD in
/-- Over a fibre-product square, a finite free module is the patched module of its triple. -/
private theorem bijective_toPatchedModule_pi (n : ℕ) :
    Function.Bijective (toPatchedModule h (Fin n → D)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun d hd ↦ funext fun i ↦ ?_
    have h₁ := congrArg (fun x ↦ piScalarRight p₁ (Fin n) (PatchedModule.fst x) i) hd
    have h₂ := congrArg (fun x ↦ piScalarRight p₂ (Fin n) (PatchedModule.snd x) i) hd
    simp only [PatchedModule.fst_toPatchedModule, PatchedModule.snd_toPatchedModule,
      PatchedModule.fst_zero, PatchedModule.snd_zero, piScalarRight_tmul, one_mul, _root_.map_zero,
      Pi.zero_apply] at h₁ h₂
    exact (hD 0 0 (by simp)).unique ⟨h₁, h₂⟩ ⟨_root_.map_zero p₁, _root_.map_zero p₂⟩
  · intro m
    have key := (commSqEquiv_one_tmul_eq_iff h (Fin n) _ _).1 (PatchedModule.apply_one_tmul_fst m)
    choose d hd using fun i ↦ (hD _ _ (key i)).exists
    refine ⟨d, PatchedModule.ext ?_ ?_⟩
    · refine (piScalarRight p₁ (Fin n)).injective (funext fun i ↦ ?_)
      simp [(hd i).1]
    · refine (piScalarRight p₂ (Fin n)).injective (funext fun i ↦ ?_)
      simp [(hd i).2]

/-- Bijectivity of `toPatchedModule` passes to direct summands. -/
private theorem bijective_toPatchedModule_of_comp_eq_id {P F : Type*} [AddCommGroup P]
    [Module D P] [AddCommGroup F] [Module D F] (i : P →ₗ[D] F) (r : F →ₗ[D] P)
    (hri : r ∘ₗ i = LinearMap.id) (hF : Function.Bijective (toPatchedModule h F)) :
    Function.Bijective (toPatchedModule h P) := by
  constructor
  · intro x y hxy
    have := congrArg (PatchedModule.map (map p₁ i) (map p₂ i) (commSqEquiv_map h i)) hxy
    rw [PatchedModule.map_toPatchedModule, PatchedModule.map_toPatchedModule] at this
    simpa [← LinearMap.comp_apply r i, hri] using congrArg r (hF.1 this)
  · intro m
    obtain ⟨f, hf⟩ :=
      hF.2 (PatchedModule.map (map p₁ i) (map p₂ i) (commSqEquiv_map h i) m)
    refine ⟨r f, ?_⟩
    rw [← PatchedModule.map_toPatchedModule h r, hf]
    ext
    · simp [← LinearMap.comp_apply (map p₁ r), ← BalancedExtension.map_comp, hri]
    · simp [← LinearMap.comp_apply (map p₂ r), ← BalancedExtension.map_comp, hri]

include hD in
/-- **A finitely generated projective module is the patched module of its triple.** Over a
fibre-product square `π₁ ∘ p₁ = π₂ ∘ p₂`, in which every pair `(a₁, a₂)` with `π₁ a₁ = π₂ a₂`
comes from exactly one element of `D`, the map `p ↦ (1 ⊗ p, 1 ⊗ p)` from a finitely generated
projective left `D`-module `P` to the patched module of `(A₁ ⊗_D P, A₂ ⊗_D P, α_P)` is
bijective. -/
theorem bijective_toPatchedModule (P : Type*) [AddCommGroup P] [Module D P] [Module.Finite D P]
    [Module.Projective D P] : Function.Bijective (toPatchedModule h P) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective D P
  exact bijective_toPatchedModule_of_comp_eq_id h g f hfg (bijective_toPatchedModule_pi h hD _)

/-- Over a fibre-product square, a finitely generated projective left `D`-module `P` is isomorphic
to the patched module of its triple `(A₁ ⊗_D P, A₂ ⊗_D P, α_P)`, by `p ↦ (1 ⊗ p, 1 ⊗ p)`. -/
noncomputable def patchedModuleEquiv (P : Type*) [AddCommGroup P] [Module D P]
    [Module.Finite D P] [Module.Projective D P] :
    P ≃ₗ[D] PatchedModule h (commSqEquiv h P).toLinearMap :=
  LinearEquiv.ofBijective (toPatchedModule h P) (bijective_toPatchedModule h hD P)

@[simp]
theorem patchedModuleEquiv_apply (P : Type*) [AddCommGroup P] [Module D P] [Module.Finite D P]
    [Module.Projective D P] (x : P) :
    patchedModuleEquiv h hD P x = toPatchedModule h P x := (rfl)

/-- `toPatchedModule` is a left inverse of the inverse of `patchedModuleEquiv`. -/
@[simp]
theorem toPatchedModule_patchedModuleEquiv_symm_apply (P : Type*) [AddCommGroup P] [Module D P]
    [Module.Finite D P] [Module.Projective D P]
    (m : PatchedModule h (commSqEquiv h P).toLinearMap) :
    toPatchedModule h P ((patchedModuleEquiv h hD P).symm m) = m :=
  (patchedModuleEquiv h hD P).apply_symm_apply m

/-- The inverse of `patchedModuleEquiv` undoes `toPatchedModule`. -/
@[simp]
theorem patchedModuleEquiv_symm_toPatchedModule (P : Type*) [AddCommGroup P] [Module D P]
    [Module.Finite D P] [Module.Projective D P] (x : P) :
    (patchedModuleEquiv h hD P).symm (toPatchedModule h P x) = x :=
  (patchedModuleEquiv h hD P).symm_apply_apply x

include hD in
/-- **Extension of scalars to patching triples is fully faithful on finitely generated projective
modules.** Over a fibre-product square, let `g₁ : A₁ ⊗_D P → A₁ ⊗_D P'` and
`g₂ : A₂ ⊗_D P → A₂ ⊗_D P'` be linear maps whose extensions to `Q` are intertwined by the gluing
isomorphisms. If `P'` is finitely generated projective, there is exactly one `D`-linear map
`g : P → P'` whose extensions are `g₁` and `g₂`. -/
theorem BalancedExtension.existsUnique_map_eq_and_map_eq {P P' : Type*} [AddCommGroup P]
    [Module D P] [AddCommGroup P'] [Module D P'] [Module.Finite D P'] [Module.Projective D P']
    (g₁ : BalancedExtension p₁ P →ₗ[A₁] BalancedExtension p₁ P')
    (g₂ : BalancedExtension p₂ P →ₗ[A₂] BalancedExtension p₂ P')
    (hg : ∀ x, commSqEquiv h P' (map π₁ g₁ x) = map π₂ g₂ (commSqEquiv h P x)) :
    ∃! g : P →ₗ[D] P', map p₁ g = g₁ ∧ map p₂ g = g₂ := by
  set g : P →ₗ[D] P' := (patchedModuleEquiv h hD P').symm.toLinearMap ∘ₗ
    PatchedModule.map g₁ g₂ hg ∘ₗ toPatchedModule h P
  have hg' (x : P) : toPatchedModule h P' (g x) = PatchedModule.map g₁ g₂ hg
      (toPatchedModule h P x) := by
    simp [g]
  refine ⟨g, ⟨hom_ext fun x ↦ ?_, hom_ext fun x ↦ ?_⟩, fun g' ⟨hg₁, hg₂⟩ ↦ ?_⟩
  · simpa using congrArg PatchedModule.fst (hg' x)
  · simpa using congrArg PatchedModule.snd (hg' x)
  · refine LinearMap.ext fun x ↦ (bijective_toPatchedModule h hD P').1 ?_
    rw [hg']
    ext
    · simp [← hg₁]
    · simp [← hg₂]

end FibreProduct

end TauCeti

namespace RingHom

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Semiring Q]

/-- The fibre product `RingHom.pullback π₁ π₂` of rings satisfies the fibre-product hypothesis of
`TauCeti.bijective_toPatchedModule`: a pair `(a₁, a₂)` with `π₁ a₁ = π₂ a₂` is the image of exactly
one of its elements. -/
theorem existsUnique_pullbackFst_eq_and_pullbackSnd_eq (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) {a₁ : A₁}
    {a₂ : A₂} (h : π₁ a₁ = π₂ a₂) :
    ∃! d : π₁.pullback π₂, π₁.pullbackFst π₂ d = a₁ ∧ π₁.pullbackSnd π₂ d = a₂ :=
  ⟨⟨(a₁, a₂), h⟩, ⟨rfl, rfl⟩, fun _ hd ↦ Subtype.ext (Prod.ext hd.1 hd.2)⟩

/-- The commuting square `π₁ ∘ p₁ = π₂ ∘ p₂` of `RingHom.pullback π₁ π₂`
(`RingHom.pullback_comm_sq`), read on opposite rings: the square over which right modules over the
fibre product are patched, as left modules over the opposite rings. -/
theorem op_pullback_comm_sq (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) :
    (RingHom.op π₁).comp (RingHom.op (π₁.pullbackFst π₂)) =
      (RingHom.op π₂).comp (RingHom.op (π₁.pullbackSnd π₂)) :=
  RingHom.ext fun x ↦ congrArg MulOpposite.op (RingHom.congr_fun (π₁.pullback_comm_sq π₂) x.unop)

/-- The square `RingHom.op_pullback_comm_sq` of opposite rings satisfies the fibre-product
hypothesis of `TauCeti.bijective_toPatchedModule`: a pair `(a₁, a₂)` of elements of `A₁ᵐᵒᵖ` and
`A₂ᵐᵒᵖ` with the same image in `Qᵐᵒᵖ` is the image of exactly one element of the opposite ring of
`RingHom.pullback π₁ π₂`. -/
theorem existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    {a₁ : A₁ᵐᵒᵖ} {a₂ : A₂ᵐᵒᵖ} (h : RingHom.op π₁ a₁ = RingHom.op π₂ a₂) :
    ∃! d : (π₁.pullback π₂)ᵐᵒᵖ,
      RingHom.op (π₁.pullbackFst π₂) d = a₁ ∧ RingHom.op (π₁.pullbackSnd π₂) d = a₂ := by
  obtain ⟨d, hd, hu⟩ :=
    existsUnique_pullbackFst_eq_and_pullbackSnd_eq π₁ π₂ (congrArg MulOpposite.unop h)
  refine ⟨MulOpposite.op d, ⟨congrArg MulOpposite.op hd.1, congrArg MulOpposite.op hd.2⟩,
    fun d' hd' ↦ congrArg MulOpposite.op (hu d'.unop ?_)⟩
  exact ⟨congrArg MulOpposite.unop hd'.1, congrArg MulOpposite.unop hd'.2⟩

end RingHom
