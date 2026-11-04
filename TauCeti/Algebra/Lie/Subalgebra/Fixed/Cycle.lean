/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import TauCeti.Algebra.Lie.Pi

/-!
# Fixed Lie algebras of component cycles

A cyclic chain of Lie homomorphisms acts on the product of its component Lie algebras.
Evaluation on the first component identifies its fixed Lie algebra with the fixed Lie
algebra of the return map. The inverse transports a vector along the chain. The component
algebras may differ, and the arrows need not be invertible.

This reduces fixed-algebra calculations for an automorphism cycling through several
components to the return automorphism on one component. No hypothesis on characteristic,
finite dimensionality, or the order of the return map is needed. A one-component cycle is
allowed and retains its possibly nonidentity return map.

The fixed carrier is `LieHom.fixedSubalgebra`, whose underlying module is Mathlib's
`LinearMap.fixedSubmodule`. For the component reduction in diagram folding, see
V. Kac, *Infinite-Dimensional Lie Algebras*, third edition, §§7.8–7.9.
-/

public section

namespace TauCeti.LieCycle

variable {R : Type*} [CommRing R] {n : ℕ}
variable {L : Fin (n + 1) → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

/-- Transport from the first component to each component along a chain of Lie maps. -/
def transport (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (i : Fin (n + 1)) : L 0 →ₗ⁅R⁆ L i :=
  Fin.induction (LieHom.id) (fun j p ↦ (f j).comp p) i

/-- Transport to the first component traverses no arrows. -/
@[simp] theorem transport_zero (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ) :
    transport f 0 = LieHom.id := (rfl)

/-- Transport to a successor appends the next arrow to the transport already performed. -/
@[simp] theorem transport_succ (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (i : Fin n) : transport f i.succ = (f i).comp (transport f i.castSucc) := (rfl)

/-- The return map traverses the chain and then its closing arrow. -/
def returnMap (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) : L 0 →ₗ⁅R⁆ L 0 :=
  g.comp (transport f (Fin.last n))

/-- The return map applies the closing arrow after transport to the last component. -/
@[simp] theorem returnMap_apply (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : L 0) :
    returnMap f g x = g (transport f (Fin.last n) x) := (rfl)

/-- If all arrows are bijective, the return map is bijective, so it defines a return
Lie automorphism via `LieEquiv.ofBijective`. -/
theorem returnMap_bijective (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (hf : ∀ i, Function.Bijective (f i))
    (hg : Function.Bijective g) : Function.Bijective (returnMap f g) := by
  have htransport (i : Fin (n + 1)) : Function.Bijective (transport f i) := by
    induction i using Fin.induction with
    | zero => simpa only [transport_zero, LieHom.coe_id] using Function.bijective_id
    | succ i ih =>
      simpa only [transport_succ, LieHom.coe_comp] using (hf i).comp ih
  exact hg.comp (htransport (Fin.last n))

/-- The cyclic shift sends each component along its outgoing Lie map. -/
def shift (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) : (∀ i, L i) →ₗ⁅R⁆ (∀ i, L i) where
  toFun x := Fin.cases (g (x (Fin.last n))) (fun i ↦ f i (x i.castSucc))
  map_add' x y := by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' t x := by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  map_lie' {x y} := by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- The zeroth coordinate of the shift comes from the closing arrow. -/
@[simp] theorem shift_apply_zero (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : ∀ i, L i) :
    shift f g x 0 = g (x (Fin.last n)) := (rfl)

/-- Each successor coordinate of the shift comes from the preceding component. -/
@[simp] theorem shift_apply_succ (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : ∀ i, L i) (i : Fin n) :
    shift f g x i.succ = f i (x i.castSucc) := (rfl)

/-- A tuple is fixed precisely when its coordinates follow the arrows, including closure. -/
theorem mem_fixedSubalgebra_shift_iff (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : ∀ i, L i) :
    x ∈ (shift f g).fixedSubalgebra ↔
      g (x (Fin.last n)) = x 0 ∧ ∀ i : Fin n, f i (x i.castSucc) = x i.succ := by
  rw [LieHom.mem_fixedSubalgebra, funext_iff, Fin.forall_fin_succ]
  simp only [shift_apply_zero, shift_apply_succ]

/-- Every coordinate of a fixed tuple is obtained by transport from its first coordinate. -/
theorem apply_eq_transport (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : (shift f g).fixedSubalgebra)
    (i : Fin (n + 1)) : x.val i = transport f i (x.val 0) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [transport_succ, LieHom.comp_apply, ← ih]
    exact ((mem_fixedSubalgebra_shift_iff f g x.val).mp x.property).2 i |>.symm

/-- A fixed tuple is exactly a transported return-fixed vector. -/
theorem mem_fixedSubalgebra_shift_iff_transport
    (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : ∀ i, L i) :
    x ∈ (shift f g).fixedSubalgebra ↔
      (∀ i, x i = transport f i (x 0)) ∧ x 0 ∈ (returnMap f g).fixedSubalgebra := by
  constructor
  · intro hx
    have hcoord := apply_eq_transport f g ⟨x, hx⟩
    refine ⟨hcoord, ?_⟩
    simpa only [LieHom.mem_fixedSubalgebra, returnMap_apply, ← hcoord] using
      ((mem_fixedSubalgebra_shift_iff f g x).mp hx).1
  · rintro ⟨hcoord, hreturn⟩
    apply (mem_fixedSubalgebra_shift_iff f g x).mpr
    constructor
    · simpa only [LieHom.mem_fixedSubalgebra, returnMap_apply, ← hcoord] using hreturn
    · intro i
      rw [hcoord i.castSucc, hcoord i.succ, transport_succ, LieHom.comp_apply]

/-- Evaluation on the first component identifies fixed tuples with fixed points of the
return map. Its inverse transports a vector along every initial segment of the cycle. -/
def fixedEquiv (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) :
    (shift f g).fixedSubalgebra ≃ₗ⁅R⁆ (returnMap f g).fixedSubalgebra where
  toFun x := ⟨x.val 0,
    ((mem_fixedSubalgebra_shift_iff_transport f g x.val).mp x.property).2⟩
  invFun x := ⟨fun i ↦ transport f i x.val, by
    apply (mem_fixedSubalgebra_shift_iff_transport f g _).mpr
    exact ⟨by simp, by simp⟩⟩
  left_inv x := Subtype.ext (funext fun i ↦ (apply_eq_transport f g x i).symm)
  right_inv x := Subtype.ext (by simp)
  map_add' x y := rfl
  map_smul' t x := rfl
  map_lie' {x y} := rfl

/-- The fixed-algebra equivalence is evaluation on the first component. -/
@[simp] theorem fixedEquiv_apply (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : (shift f g).fixedSubalgebra) :
    (fixedEquiv f g x).val = x.val 0 := (rfl)

/-- The inverse fixed-algebra equivalence is the specified transport in every component. -/
@[simp] theorem fixedEquiv_symm_apply (f : ∀ i : Fin n, L i.castSucc →ₗ⁅R⁆ L i.succ)
    (g : L (Fin.last n) →ₗ⁅R⁆ L 0) (x : (returnMap f g).fixedSubalgebra)
    (i : Fin (n + 1)) : ((fixedEquiv f g).symm x).val i = transport f i x.val := (rfl)

end TauCeti.LieCycle
