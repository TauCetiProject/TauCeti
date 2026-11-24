/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Subtype and fiber equivalences

Restricting a type `E` first to the elements satisfying `p` and then to those satisfying `q`
leaves the same elements as restricting in the opposite order. When the second predicate in each
order is stated on the subtype, rather than on `E`, this is the equivalence
`Equiv.subtypeSubtypeComm`; it identifies, for instance, the edges left after deleting two vertices
of a graph one after the other, in either order.

A function `f : α → β` with `f i = f j` at two distinct points is determined by its values away
from `j`, since its value at `j` is its value at `i`. The equivalence
`Equiv.subtypeApplyEqApplyEquivFun` restricts such functions to `{a // a ≠ j}`; it counts the
functions identifying two given points, as in collision bounds for uniform sampling.

Equivalences `e : α ≃ β` intertwining maps `f : α → γ` and `g : β → γ` correspond to families of
fiber equivalences `{a // f a = c} ≃ {b // g b = c}` (`Equiv.fiberEquiv`), upgrading
`Equiv.ofFiberEquiv` to a two-way equivalence; specializing to `Sigma.fst` identifies equivalences
`α ≃ Σ i, β i` with prescribed first projection `f` as families `{a // f a = i} ≃ β i`
(`Equiv.fiberEquivSigma`).

The file also records that the transposition of two points of a linear order is the transposition
of their minimum and maximum (`Equiv.swap_min_max`), and that an equivalence and an injective map
intertwining two functions transport preimage witnesses (`Equiv.exists_eq_and_iff_of_injective`).
-/

public section

namespace Equiv

/-- Removing the elements failing `p` and then those failing `q` leaves the same elements as
removing them in the opposite order. The predicates `q'` on `Subtype p` and `p'` on `Subtype q`
are the restrictions of `q` and `p`. -/
def subtypeSubtypeComm {E : Type*} {p q : E → Prop} {p' : Subtype q → Prop}
    {q' : Subtype p → Prop} (hp : ∀ e he, p' ⟨e, he⟩ ↔ p e) (hq : ∀ e he, q' ⟨e, he⟩ ↔ q e) :
    {e : Subtype p // q' e} ≃ {e : Subtype q // p' e} :=
  (subtypeSubtypeEquivSubtypeExists p q').trans <|
    (subtypeEquivRight fun e ↦
      ⟨fun ⟨hpe, hqe⟩ ↦ ⟨(hq e hpe).mp hqe, (hp e _).mpr hpe⟩,
        fun ⟨hqe, hpe⟩ ↦ ⟨(hp e hqe).mp hpe, (hq e _).mpr hqe⟩⟩).trans
      (subtypeSubtypeEquivSubtypeExists q p').symm

/-- `Equiv.subtypeSubtypeComm` does not move the underlying element of `E`. -/
@[simp]
theorem coe_coe_subtypeSubtypeComm_apply {E : Type*} {p q : E → Prop} {p' : Subtype q → Prop}
    {q' : Subtype p → Prop} (hp : ∀ e he, p' ⟨e, he⟩ ↔ p e) (hq : ∀ e he, q' ⟨e, he⟩ ↔ q e)
    (e : {e : Subtype p // q' e}) : ((subtypeSubtypeComm hp hq e : Subtype q) : E) = e.val.val :=
  (rfl)

/-- The inverse of `Equiv.subtypeSubtypeComm` does not move the underlying element of `E`. -/
@[simp]
theorem coe_coe_subtypeSubtypeComm_symm_apply {E : Type*} {p q : E → Prop}
    {p' : Subtype q → Prop} {q' : Subtype p → Prop} (hp : ∀ e he, p' ⟨e, he⟩ ↔ p e)
    (hq : ∀ e he, q' ⟨e, he⟩ ↔ q e) (e : {e : Subtype q // p' e}) :
    (((subtypeSubtypeComm hp hq).symm e : Subtype p) : E) = e.val.val :=
  (rfl)

section subtypeApplyEqApplyEquivFun

variable {α β : Sort*} [DecidableEq α] {i j : α}

/-- The functions `f : α → β` with `f i = f j` at two distinct points `i` and `j` are equivalent to
the functions on `{a // a ≠ j}`: such an `f` is restricted to the points other than `j`, and a
function `g` on them is extended by its value at `i`. -/
def subtypeApplyEqApplyEquivFun (hij : i ≠ j) :
    {f : α → β // f i = f j} ≃ ({a // a ≠ j} → β) where
  toFun f a := f.val a
  invFun g := ⟨fun a ↦ if ha : a = j then g ⟨i, hij⟩ else g ⟨a, ha⟩, by simp [hij]⟩
  left_inv := fun ⟨f, (hf : f i = f j)⟩ ↦ by
    ext a
    by_cases ha : a = j <;> simp [ha, hf]
  right_inv g := by
    funext a
    simp [a.property]

/-- `Equiv.subtypeApplyEqApplyEquivFun` restricts a function to the points other than `j`. -/
@[simp]
theorem subtypeApplyEqApplyEquivFun_apply (hij : i ≠ j) (f : {f : α → β // f i = f j})
    (a : {a // a ≠ j}) : subtypeApplyEqApplyEquivFun hij f a = f.val a :=
  (rfl)

/-- The inverse of `Equiv.subtypeApplyEqApplyEquivFun` extends a function on the points other
than `j` by its value at `i`. -/
@[simp]
theorem coe_subtypeApplyEqApplyEquivFun_symm_apply (hij : i ≠ j) (g : {a // a ≠ j} → β) (a : α) :
    ((subtypeApplyEqApplyEquivFun hij).symm g : α → β) a =
      if ha : a = j then g ⟨i, hij⟩ else g ⟨a, ha⟩ :=
  (rfl)

end subtypeApplyEqApplyEquivFun

/-- The transposition of two points of a linear order, written with the smaller point first. -/
theorem swap_min_max {α : Type*} [LinearOrder α] (a b : α) :
    swap (min a b) (max a b) = swap a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, swap_comm]

/-- Equivalences `e : α ≃ β` intertwining `f : α → γ` and `g : β → γ` correspond to
families of equivalences between the corresponding fibers `{a // f a = c} ≃ {b // g b = c}`. -/
def fiberEquiv {α β γ : Type*} (f : α → γ) (g : β → γ) :
    {e : α ≃ β // ∀ a, g (e a) = f a} ≃ ∀ c : γ, {a // f a = c} ≃ {b // g b = c} where
  toFun e _ := e.val.subtypeEquiv fun a ↦ by rw [e.property]
  invFun e := ⟨ofFiberEquiv e, fun a ↦ ofFiberEquiv_map e a⟩
  left_inv _ := Subtype.ext <| Equiv.ext fun _ ↦ rfl
  right_inv _ := funext fun _ ↦ Equiv.ext fun ⟨_, ha⟩ ↦ by subst ha; rfl

/-- Applying `Equiv.fiberEquiv` on a fiber `c` applies the underlying equivalence. -/
@[simp]
theorem coe_fiberEquiv_apply_apply {α β γ : Type*} (f : α → γ) (g : β → γ)
    (e : {e : α ≃ β // ∀ a, g (e a) = f a}) (c : γ) (a : {a // f a = c}) :
    ((fiberEquiv f g e c a : {b // g b = c}) : β) = e.val a.val :=
  (rfl)

/-- The inverse of the fiber equivalence `Equiv.fiberEquiv f g e c` applies the inverse of the
underlying equivalence `e`. -/
@[simp]
theorem coe_fiberEquiv_apply_symm_apply {α β γ : Type*} (f : α → γ) (g : β → γ)
    (e : {e : α ≃ β // ∀ a, g (e a) = f a}) (c : γ) (b : {b // g b = c}) :
    (((fiberEquiv f g e c).symm b : {a // f a = c}) : α) = e.val.symm b.val :=
  (rfl)

/-- The inverse of `Equiv.fiberEquiv` is `Equiv.ofFiberEquiv`. -/
@[simp]
theorem coe_fiberEquiv_symm_apply {α β γ : Type*} (f : α → γ) (g : β → γ)
    (e : ∀ c : γ, {a // f a = c} ≃ {b // g b = c}) :
    ((fiberEquiv f g).symm e : α ≃ β) = ofFiberEquiv e :=
  (rfl)

/-- The inverse of `Equiv.sigmaSubtype` pairs the fiber element with the pinned base point. -/
@[simp]
theorem sigmaSubtype_symm_apply {α : Type*} {β : α → Type*} (a : α) (b : β a) :
    (sigmaSubtype a).symm b = ⟨⟨a, b⟩, rfl⟩ :=
  (rfl)

/-- Reconstructing a sigma pair from `Equiv.sigmaSubtype` recovers the underlying element. -/
theorem sigma_mk_sigmaSubtype {α : Type*} {β : α → Type*} (a : α)
    (s : {p : Σ i, β i // p.1 = a}) :
    (⟨a, sigmaSubtype a s⟩ : Σ i, β i) = s.val := by
  rcases s with ⟨⟨_, _⟩, rfl⟩
  rfl

/-- Equivalences `e : α ≃ Σ i, β i` whose first projection agrees with `f : α → ι` correspond to
families of fiber equivalences `{a // f a = i} ≃ β i`. -/
def fiberEquivSigma {α ι : Type*} {β : ι → Type*} (f : α → ι) :
    {e : α ≃ Σ i, β i // ∀ a, (e a).1 = f a} ≃ ∀ i : ι, {a // f a = i} ≃ β i :=
  (fiberEquiv f Sigma.fst).trans <|
    piCongrRight fun i ↦ equivCongr (Equiv.refl _) (sigmaSubtype i)

/-- Reconstructing the sigma pair from `Equiv.fiberEquivSigma` recovers the image under the
underlying equivalence `e`. -/
@[simp]
theorem sigma_mk_fiberEquivSigma_apply_apply {α ι : Type*} {β : ι → Type*} (f : α → ι)
    (e : {e : α ≃ Σ i, β i // ∀ a, (e a).1 = f a}) (i : ι) (a : {a // f a = i}) :
    (⟨i, fiberEquivSigma f e i a⟩ : Σ i, β i) = e.val a.val :=
  (sigma_mk_sigmaSubtype i (fiberEquiv f Sigma.fst e i a)).trans
    (coe_fiberEquiv_apply_apply f Sigma.fst e i a)

/-- The inverse of the fiber equivalence `Equiv.fiberEquivSigma f e i` applies the inverse of the
underlying equivalence `e` on the `i`-th fiber. -/
@[simp]
theorem coe_fiberEquivSigma_apply_symm_apply {α ι : Type*} {β : ι → Type*} (f : α → ι)
    (e : {e : α ≃ Σ i, β i // ∀ a, (e a).1 = f a}) (i : ι) (b : β i) :
    (((fiberEquivSigma f e i).symm b : {a // f a = i}) : α) = e.val.symm ⟨i, b⟩ :=
  (rfl)

/-- Applying the equivalence reconstructed by `(Equiv.fiberEquivSigma f).symm e` to `a` places
`e (f a) ⟨a, rfl⟩` in fiber `f a`. -/
@[simp]
theorem coe_fiberEquivSigma_symm_apply_apply {α ι : Type*} {β : ι → Type*} (f : α → ι)
    (e : ∀ i : ι, {a // f a = i} ≃ β i) (a : α) :
    ((fiberEquivSigma f).symm e : α ≃ Σ i, β i) a = ⟨f a, e (f a) ⟨a, rfl⟩⟩ :=
  (rfl)

/-- Applying the inverse of the equivalence reconstructed by `(Equiv.fiberEquivSigma f).symm e` to
`p` applies `(e p.1).symm` to `p.2`. -/
@[simp]
theorem coe_fiberEquivSigma_symm_apply_symm_apply {α ι : Type*} {β : ι → Type*} (f : α → ι)
    (e : ∀ i : ι, {a // f a = i} ≃ β i) (p : Σ i, β i) :
    ((fiberEquivSigma f).symm e : α ≃ Σ i, β i).symm p = ((e p.1).symm p.2).val := by
  rcases p with ⟨i, b⟩
  rfl

/-- Transporting a preimage witness along an equivalence `eA : α ≃ α₀` and an injective map
`eB : β → β₀` that intertwine `F : α → β` with `F₀ : α₀ → β₀`: a preimage of `b` under `F`
satisfying `P (eA a)` exists if and only if a preimage of `eB b` under `F₀` satisfying `P a₀`
exists. -/
theorem exists_eq_and_iff_of_injective {α β α₀ β₀ : Sort*} {F : α → β} {F₀ : α₀ → β₀}
    (eA : α ≃ α₀) {eB : β → β₀} (heB : Function.Injective eB)
    (hF : ∀ a, eB (F a) = F₀ (eA a)) {P : α₀ → Prop} {b : β} :
    (∃ a, F a = b ∧ P (eA a)) ↔ ∃ a₀, F₀ a₀ = eB b ∧ P a₀ :=
  eA.exists_congr fun a ↦ by rw [← heB.eq_iff, hF]

end Equiv
