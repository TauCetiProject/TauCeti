/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Permutation wreath products

Let `D` be a group and let a group `Q` act on an index type `ι` by permutations. The associated
permutation wreath product is the semidirect product

`(ι → D) ⋊ Q`,

where `Q` permutes the coordinates of the base group. This file defines the full wreath product
with `Q = Equiv.Perm ι` and the wreath product attached to a permutation subgroup
`Q ≤ Equiv.Perm ι`.

The semidirect-product API supplies the inclusions of the base and top groups and the projection
to the top group. Two natural actions are defined here. If `D` acts on `Λ`, the imprimitive action
is on `ι × Λ`, while the product action is on `ι → Λ`. These constructions are kept separate;
primitivity of the product action requires additional hypotheses and is not asserted here.

## Main definitions

* `TauCeti.WreathProduct`: the full permutation wreath product `(ι → D) ⋊ Equiv.Perm ι`.
* `TauCeti.PermSubgroupWreathProduct`: the wreath product whose top group is a subgroup of
  `Equiv.Perm ι`.
* `TauCeti.WreathProduct.imprimitiveToPerm`: the imprimitive permutation representation on
  `ι × Λ`.
* `TauCeti.WreathProduct.productToPerm`: the product permutation representation on `ι → Λ`.

The convention agrees with `Mathlib.GroupTheory.RegularWreathProduct`: an element `(a, q)` acts
on the base by `b i ↦ b (q⁻¹ i)`. In the imprimitive action it sends `(i, x)` to
`(q i, a (q i) • x)`.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §2.6.
-/

public section

namespace TauCeti

universe u v w

variable (D : Type u) (ι : Type v) [Group D]

/-- The full permutation wreath product of `D` by the symmetric group on `ι`. Its base group is
`ι → D`, and its top group is `Equiv.Perm ι`. -/
abbrev WreathProduct :=
  (ι → D) ⋊[mulAutArrow (G := Equiv.Perm ι) (A := ι) (M := D)] Equiv.Perm ι

/-- The permutation wreath product with top group restricted to
`Q ≤ Equiv.Perm ι`. -/
abbrev PermSubgroupWreathProduct (Q : Subgroup (Equiv.Perm ι)) :=
  (ι → D) ⋊[(mulAutArrow (G := Equiv.Perm ι) (A := ι) (M := D)).comp Q.subtype] Q

namespace WreathProduct

variable {D ι}

/-- Multiplication in a permutation wreath product, written in coordinates. -/
@[simp]
theorem mul_left (a b : WreathProduct D ι) (i : ι) :
    (a * b).left i = a.left i * b.left (a.right⁻¹ i) := by
  have h := congrFun (SemidirectProduct.mul_left a b) i
  rw [Pi.mul_apply] at h
  rw [mulAutArrow_apply_apply] at h
  exact h

/-- The natural cardinality of a full permutation wreath product with finite index type. -/
theorem card [Finite ι] :
    Nat.card (WreathProduct D ι) =
      Nat.card D ^ Nat.card ι * (Nat.card ι).factorial := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_perm]

end WreathProduct

namespace PermSubgroupWreathProduct

variable {D ι}

/-- Multiplication in a permutation-subgroup wreath product, written in coordinates. -/
@[simp]
theorem mul_left (Q : Subgroup (Equiv.Perm ι)) (a b : PermSubgroupWreathProduct D ι Q) (i : ι) :
    (a * b).left i = a.left i * b.left ((a.right : Equiv.Perm ι)⁻¹ i) := by
  have h := congrFun (SemidirectProduct.mul_left a b) i
  rw [Pi.mul_apply] at h
  rw [MonoidHom.comp_apply, mulAutArrow_apply_apply] at h
  exact h

/-- The natural cardinality of a permutation-subgroup wreath product with finite index type. -/
theorem card (Q : Subgroup (Equiv.Perm ι)) [Finite ι] :
    Nat.card (PermSubgroupWreathProduct D ι Q) =
      Nat.card D ^ Nat.card ι * Nat.card Q := by
  rw [SemidirectProduct.card, Nat.card_fun]

end PermSubgroupWreathProduct

namespace WreathProduct

variable {D ι}

/-- A wreath product over the empty index type is the trivial group. -/
def emptyEquiv : WreathProduct D Empty ≃* PUnit where
  toFun _ := PUnit.unit
  invFun _ := 1
  left_inv w := by
    apply SemidirectProduct.ext
    · funext i
      exact i.elim
    · apply Equiv.ext
      intro i
      exact i.elim
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem emptyEquiv_apply (w : WreathProduct D Empty) : emptyEquiv w = PUnit.unit := by
  simp [emptyEquiv]

/-- The inverse empty-index equivalence has trivial base component. -/
@[simp]
theorem emptyEquiv_symm_left (x : PUnit) :
    (emptyEquiv.symm x : WreathProduct D Empty).left = 1 := by
  simp [emptyEquiv]

/-- The inverse empty-index equivalence has trivial top permutation. -/
@[simp]
theorem emptyEquiv_symm_right (x : PUnit) :
    (emptyEquiv.symm x : WreathProduct D Empty).right = 1 := by
  simp [emptyEquiv]

/-- A wreath product over a singleton index type is canonically isomorphic to its base group. -/
def finOneEquiv : WreathProduct D (Fin 1) ≃* D where
  toFun w := w.left 0
  invFun d := ⟨fun _ ↦ d, 1⟩
  left_inv w := by
    apply SemidirectProduct.ext
    · funext i
      exact congrArg w.left (Subsingleton.elim 0 i)
    · exact Subsingleton.elim _ _
  right_inv _ := rfl
  map_mul' w z := by
    rw [mul_left]
    congr 1
    exact congrArg z.left (Subsingleton.elim _ _)

@[simp]
theorem finOneEquiv_apply (w : WreathProduct D (Fin 1)) : finOneEquiv w = w.left 0 := by
  simp [finOneEquiv]

@[simp]
theorem finOneEquiv_symm_left (d : D) :
    (finOneEquiv.symm d).left = fun _ ↦ d := by
  simp [finOneEquiv]

/-- The inverse singleton-index equivalence has trivial top permutation. -/
@[simp]
theorem finOneEquiv_symm_right (d : D) :
    (finOneEquiv.symm d).right = 1 := by
  simp [finOneEquiv]

/-- A wreath product with a trivial base group is canonically isomorphic to its top symmetric
group. -/
def subsingletonBaseEquiv [Subsingleton D] : WreathProduct D ι ≃* Equiv.Perm ι :=
  MonoidHom.toMulEquiv SemidirectProduct.rightHom SemidirectProduct.inr
    (by
      ext w
      · exact Subsingleton.elim _ _
      · simp)
    (by ext; simp)

@[simp]
theorem subsingletonBaseEquiv_apply [Subsingleton D] (w : WreathProduct D ι) :
    subsingletonBaseEquiv w = w.right := by
  simp [subsingletonBaseEquiv]

/-- The inverse trivial-base equivalence has trivial base component. -/
@[simp]
theorem subsingletonBaseEquiv_symm_left [Subsingleton D] (σ : Equiv.Perm ι) :
    (subsingletonBaseEquiv.symm σ : WreathProduct D ι).left = 1 := by
  simp [subsingletonBaseEquiv]

/-- The inverse trivial-base equivalence preserves the top permutation. -/
@[simp]
theorem subsingletonBaseEquiv_symm_right [Subsingleton D] (σ : Equiv.Perm ι) :
    (subsingletonBaseEquiv.symm σ : WreathProduct D ι).right = σ := by
  simp [subsingletonBaseEquiv]

section Functoriality

variable {D' : Type*} [Group D']

/-- A group homomorphism of base groups induces a homomorphism of full permutation wreath
products, acting pointwise on the base and identically on the top group. -/
def map (f : D →* D') : WreathProduct D ι →* WreathProduct D' ι :=
  SemidirectProduct.map (MonoidHom.piMap fun _ ↦ f) (MonoidHom.id _) fun σ ↦ by
    ext b i
    rfl

/-- Mapping the base group acts pointwise on the base coordinates. -/
@[simp]
theorem map_left (f : D →* D') (w : WreathProduct D ι) (i : ι) :
    (map f w).left i = f (w.left i) := by
  simp [map]

/-- Mapping the base group leaves the top permutation unchanged. -/
@[simp]
theorem map_right (f : D →* D') (w : WreathProduct D ι) :
    (map f w).right = w.right := by
  simp [map]

/-- Mapping by the identity homomorphism is the identity on the wreath product. -/
@[simp]
theorem map_id : map (MonoidHom.id D) = MonoidHom.id (WreathProduct D ι) := by
  ext w <;> simp

/-- Mapping the base group along a composite homomorphism is the composite of the induced wreath
product homomorphisms. -/
@[simp]
theorem map_comp {D'' : Type*} [Group D''] (g : D' →* D'') (f : D →* D') :
    map (g.comp f) = (map g).comp (map f : WreathProduct D ι →* WreathProduct D' ι) := by
  ext w <;> simp

end Functoriality

section Relabel

variable {κ : Type w}

/-- Relabeling the index type induces an isomorphism of full permutation wreath products. -/
def congr (e : ι ≃ κ) : WreathProduct D ι ≃* WreathProduct D κ :=
  SemidirectProduct.congr (MulEquiv.arrowCongr e (MulEquiv.refl D)) e.permCongrHom fun σ ↦ by
    ext f i
    -- Unfold the arrow action, relabeling equivalence, and permutation-congruence coercions to
    -- expose the equality of coordinate evaluations proved below.
    change f (σ⁻¹ (e.symm i)) = f (e.symm ((e.permCongrHom σ)⁻¹ i))
    rw [← map_inv e.permCongrHom σ]
    simp [Equiv.permCongrHom, Equiv.permCongr_apply]

/-- The base coordinates of a relabeled wreath-product element are relabeled by `e`. -/
@[simp]
theorem congr_left (e : ι ≃ κ) (w : WreathProduct D ι) (i : κ) :
    (congr e w).left i = w.left (e.symm i) := by
  simp [congr]

/-- The top permutation of a relabeled wreath-product element is conjugated by `e`. -/
@[simp]
theorem congr_right (e : ι ≃ κ) (w : WreathProduct D ι) :
    (congr e w).right = e.permCongr w.right := by
  simp [congr]

/-- Relabeling by the identity equivalence is the identity isomorphism. -/
@[simp]
theorem congr_refl : congr (Equiv.refl ι) = MulEquiv.refl (WreathProduct D ι) := by
  ext w <;> simp

/-- Successive relabelings compose to the relabeling by the composite equivalence. -/
@[simp]
theorem congr_trans {μ : Type*} (e : ι ≃ κ) (e' : κ ≃ μ) :
    (congr (D := D) e).trans (congr (D := D) e') = congr (D := D) (e.trans e') := by
  ext w <;> simp

end Relabel

section Imprimitive

variable (D ι) (Λ : Type w) [MulAction D Λ]

/-- The scalar action underlying the imprimitive action of `D ≀ Sym(ι)` on `ι × Λ`. -/
instance : SMul (WreathProduct D ι) (ι × Λ) where
  smul w x := (w.right x.1, w.left (w.right x.1) • x.2)

/-- The imprimitive action of `D ≀ Sym(ι)` on `ι × Λ`. The base group acts independently inside
each fibre `{i} × Λ`, and the top group permutes those fibres. -/
instance : MulAction (WreathProduct D ι) (ι × Λ) where
  one_smul x := by
    -- During construction Lean does not unfold the separately registered scalar action unless
    -- its formula is made explicit.
    change ((1 : WreathProduct D ι).right x.1,
      (1 : WreathProduct D ι).left ((1 : Equiv.Perm ι) x.1) • x.2) = x
    simp
  mul_smul w z x := by
    -- Expose the same formula so the semidirect multiplication and the action law of `D` apply.
    change ((w * z).right x.1, (w * z).left ((w * z).right x.1) • x.2) =
      (w.right (z.right x.1),
        w.left (w.right (z.right x.1)) • (z.left (z.right x.1) • x.2))
    ext
    · simp [Equiv.Perm.mul_apply]
    · simp only [SemidirectProduct.mul_right, Equiv.Perm.coe_mul, Function.comp_apply,
        SemidirectProduct.mul_left, Pi.mul_apply, mulAutArrow_apply_apply]
      -- `simp only` leaves the coordinate action as `(w.right • z.left) _`; this `change`
      -- unfolds it to evaluation of `z.left` at the inverse-permuted coordinate.
      change (w.left (w.right (z.right x.1)) *
        z.left (w.right⁻¹ (w.right (z.right x.1)))) • x.2 = _
      simp [mul_smul]

/-- Evaluation formula for the imprimitive wreath-product action on `ι × Λ`. -/
@[simp]
theorem imprimitive_smul (w : WreathProduct D ι) (x : ι × Λ) :
    w • x = (w.right x.1, w.left (w.right x.1) • x.2) :=
  rfl

/-- The permutation representation of the imprimitive wreath-product action on `ι × Λ`. -/
def imprimitiveToPerm : WreathProduct D ι →* Equiv.Perm (ι × Λ) :=
  MulAction.toPermHom (WreathProduct D ι) (ι × Λ)

/-- The imprimitive permutation representation evaluates via the imprimitive action. -/
@[simp]
theorem imprimitiveToPerm_apply (w : WreathProduct D ι) (x : ι × Λ) :
    imprimitiveToPerm D ι Λ w x = (w.right x.1, w.left (w.right x.1) • x.2) :=
  imprimitive_smul D ι Λ w x

/-- If the action of `D` on a nonempty `Λ` is faithful, then the imprimitive wreath-product
action is faithful. -/
instance [Nonempty Λ] [FaithfulSMul D Λ] :
    FaithfulSMul (WreathProduct D ι) (ι × Λ) where
  eq_of_smul_eq_smul {w z} h := by
    have hright : w.right = z.right := by
      obtain ⟨x⟩ := ‹Nonempty Λ›
      exact Equiv.ext fun i ↦ congrArg Prod.fst (h (i, x))
    apply SemidirectProduct.ext
    · funext i
      apply (smul_left_injective' (M := D) (α := Λ))
      funext x
      have hw : w.right (w.right⁻¹ i) = i := by
        -- Group inversion on `Equiv.Perm` is the inverse equivalence.
        change w.right (w.right.symm i) = i
        exact w.right.apply_symm_apply i
      have hz : z.right (w.right⁻¹ i) = i := by
        rw [← hright]
        exact hw
      simpa only [imprimitive_smul, hw, hz] using
        congrArg Prod.snd (h (w.right⁻¹ i, x))
    · exact hright

/-- The imprimitive permutation representation is injective when the action on each nonempty
fibre is faithful. -/
theorem imprimitiveToPerm_injective [Nonempty Λ] [FaithfulSMul D Λ] :
    Function.Injective (imprimitiveToPerm D ι Λ) :=
  MulAction.toPerm_injective

end Imprimitive

section Product

variable (D ι) (Λ : Type w) [MulAction D Λ]

/-- The scalar action underlying the product action of `D ≀ Sym(ι)` on `ι → Λ`. -/
instance : SMul (WreathProduct D ι) (ι → Λ) where
  smul w x := fun i ↦ w.left i • x (w.right⁻¹ i)

/-- The product action of `D ≀ Sym(ι)` on `ι → Λ`. The top permutation rearranges the arguments,
and the base group acts pointwise on the resulting values. -/
instance : MulAction (WreathProduct D ι) (ι → Λ) where
  one_smul x := by
    -- During construction Lean does not unfold the separately registered scalar action unless
    -- its formula is made explicit.
    change (fun i ↦ (1 : WreathProduct D ι).left i •
      x ((1 : WreathProduct D ι).right⁻¹ i)) = x
    simp
  mul_smul w z x := by
    -- Expose the same formula so the semidirect multiplication and the action law of `D` apply.
    change (fun i ↦ (w * z).left i • x ((w * z).right⁻¹ i)) =
      fun i ↦ w.left i • (z.left (w.right⁻¹ i) •
        x (z.right⁻¹ (w.right⁻¹ i)))
    funext i
    simp only [SemidirectProduct.mul_left, Pi.mul_apply, mulAutArrow_apply_apply,
      SemidirectProduct.mul_right, mul_inv_rev, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
      Function.comp_apply]
    -- `simp only` leaves `(w.right • z.left) i` and writes inverse permutations as `Equiv.symm`;
    -- this `change` unfolds the coordinate action and restores group-inverse notation.
    change (w.left i * z.left (w.right⁻¹ i)) • x (z.right⁻¹ (w.right⁻¹ i)) = _
    simp [mul_smul]

/-- Evaluation formula for the product wreath-product action on `ι → Λ`. -/
@[simp]
theorem product_smul (w : WreathProduct D ι) (x : ι → Λ) (i : ι) :
    (w • x) i = w.left i • x (w.right⁻¹ i) :=
  rfl

/-- The permutation representation of the product wreath-product action on `ι → Λ`. -/
def productToPerm : WreathProduct D ι →* Equiv.Perm (ι → Λ) :=
  MulAction.toPermHom (WreathProduct D ι) (ι → Λ)

/-- The product permutation representation evaluates via the product action. -/
@[simp]
theorem productToPerm_apply (w : WreathProduct D ι) (x : ι → Λ) (i : ι) :
    productToPerm D ι Λ w x i = w.left i • x (w.right⁻¹ i) :=
  product_smul D ι Λ w x i

/-- If `D` acts faithfully on a type with at least two elements, then the product wreath-product
action is faithful. -/
instance [Nontrivial Λ] [FaithfulSMul D Λ] :
    FaithfulSMul (WreathProduct D ι) (ι → Λ) where
  eq_of_smul_eq_smul {w z} h := by
    classical
    have hleft : w.left = z.left := by
      funext i
      apply (smul_left_injective' (M := D) (α := Λ))
      funext x
      let c : ι → Λ := fun _ ↦ x
      simpa only [product_smul] using congrFun (h c) i
    have hinv : w.right⁻¹ = z.right⁻¹ := by
      apply Equiv.ext
      intro i
      by_contra hne
      obtain ⟨x, y, hxy⟩ := exists_pair_ne Λ
      let c : ι → Λ := fun j ↦ if j = w.right⁻¹ i then x else y
      have heval : c (w.right⁻¹ i) = c (z.right⁻¹ i) := by
        apply smul_left_cancel (w.left i)
        simpa only [product_smul, hleft] using congrFun (h c) i
      have hne' : (Equiv.symm z.right) i ≠ (Equiv.symm w.right) i := by
        simpa only [Equiv.Perm.coe_inv] using Ne.symm hne
      exact hxy (by simpa [c, hne'] using heval)
    apply SemidirectProduct.ext hleft
    exact inv_injective hinv

/-- The product permutation representation is injective when the base action is faithful, the
acted-on type has at least two elements. -/
theorem productToPerm_injective [Nontrivial Λ] [FaithfulSMul D Λ] :
    Function.Injective (productToPerm D ι Λ) :=
  MulAction.toPerm_injective

end Product

end WreathProduct

end TauCeti
