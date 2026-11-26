/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
-- Private: finite-product helpers, `ZMod 3` case split, permutation trace, and involution trace.
import TauCeti.Data.Fin.Basic
import TauCeti.Data.ZMod.Three
import TauCeti.LinearAlgebra.Trace.Idempotent
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Universal presentation, basis and dimension of `cubicFixed`, and surjectivity of `cubicHom`

Building on `TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file supplies:

* The inversion-orbit basis `cubicFixedBasis N` of `cubicFixed N` indexed by `CubicOrbit N` and the
  dimension formula `finrank_cubicFixed : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* The universal property `liftSite` of `CubicTorus N` on the site unitaries `cubicSite N`,
  together with `adjoin_range_cubicSite` and `algHom_ext_cubicSite`.
* Generation of `cubicFixed N` by the spectral projections (`adjoin_range_cubicProjection`), and
  surjectivity of `cubicHom m` (`cubicHom_surjective`).

## Main definitions and results

* `TauCeti.TemperleyLieb.cubicOrbitSetoid`, `TauCeti.TemperleyLieb.CubicOrbit`,
  `TauCeti.TemperleyLieb.cubicFixedBasis`, `TauCeti.TemperleyLieb.finrank_cubicFixed`.
* `TauCeti.TemperleyLieb.liftSite`, `TauCeti.TemperleyLieb.adjoin_range_cubicSite`,
  `TauCeti.TemperleyLieb.algHom_ext_cubicSite`.
* `TauCeti.TemperleyLieb.adjoin_range_cubicProjection`,
  `TauCeti.TemperleyLieb.cubicHom_surjective`.
-/

public section

namespace TauCeti.TemperleyLieb

open Multiplicative TwistedMonoidAlgebra

/-! ### Inversion-orbit basis and dimension of `cubicFixed N` -/

/-- The inversion-orbit equivalence relation on `Fin N → ZMod 3`, identifying `a` with `±a`. -/
def cubicOrbitSetoid (N : ℕ) : Setoid (Fin N → ZMod 3) where
  r a b := a = b ∨ a = -b
  iseqv :=
    ⟨fun _ ↦ Or.inl rfl,
      fun h ↦ h.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr (neg_eq_iff_eq_neg.mp h.symm)),
      fun h₁ h₂ ↦ by
        rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl (neg_neg _)⟩

instance (N : ℕ) : DecidableRel (cubicOrbitSetoid N).r := fun a b ↦
  inferInstanceAs (Decidable (a = b ∨ a = -b))

theorem cubicOrbitSetoid_r_iff (N : ℕ) (a b : Fin N → ZMod 3) :
    (cubicOrbitSetoid N).r a b ↔ a = b ∨ a = -b :=
  (Iff.rfl)

/-- The type of inversion orbits `{a, -a}` in `Fin N → ZMod 3`, indexing a basis of
`cubicFixed N`. -/
abbrev CubicOrbit (N : ℕ) := Quotient (cubicOrbitSetoid N)

@[simp]
theorem CubicOrbit.mk_eq_mk_iff {N : ℕ} {a b : Fin N → ZMod 3} :
    (⟦a⟧ : CubicOrbit N) = ⟦b⟧ ↔ a = b ∨ a = -b :=
  Quotient.eq.trans (cubicOrbitSetoid_r_iff N a b)

/-- Symmetrized Weyl element `S(a) = W(a) + W(-a)` in `CubicTorus N`. -/
private noncomputable def symmWeyl (N : ℕ) (a : Fin N → ZMod 3) : CubicTorus N :=
  weyl N a + weyl N (-a)

private theorem symmWeyl_neg (N : ℕ) (a : Fin N → ZMod 3) :
    symmWeyl N (-a) = symmWeyl N a := by simp [symmWeyl, add_comm]

private theorem symmWeyl_zero (N : ℕ) : symmWeyl N 0 = (2 : ℂ) • 1 := by
  simp [symmWeyl, two_smul]

private theorem symmWeyl_mem_cubicFixed (N : ℕ) (a : Fin N → ZMod 3) :
    symmWeyl N a ∈ cubicFixed N := by
  rw [symmWeyl, mem_cubicFixed, map_add, cubicInversion_weyl, cubicInversion_weyl, neg_neg,
    add_comm]

private noncomputable def symmWeylFixed (N : ℕ) (a : Fin N → ZMod 3) : cubicFixed N :=
  ⟨symmWeyl N a, symmWeyl_mem_cubicFixed N a⟩

private theorem eq_zero_of_neg_eq_self {N : ℕ} {a : Fin N → ZMod 3} (h : -a = a) : a = 0 :=
  funext fun i ↦ ((ZMod.neg_eq_self_iff (a i)).mp (congrFun h i)).resolve_right (by omega)

private noncomputable def cubicOrbitVec (N : ℕ) : CubicOrbit N → cubicFixed N :=
  Quotient.lift
    (fun a ↦ if a = 0 then 1 else symmWeylFixed N a)
    (fun a b h ↦ Subtype.ext <| by
      rcases h with rfl | rfl
      · rfl
      · by_cases hb : b = 0
        · simp [hb]
        · have hnb : -b ≠ 0 := neg_ne_zero.mpr hb
          simp [hb, hnb, symmWeylFixed, symmWeyl_neg])

private theorem repr_cubicOrbitVec (N : ℕ) (q : CubicOrbit N) (a : Fin N → ZMod 3) :
    (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).repr
        (cubicOrbitVec N q : CubicTorus N) (ofAdd a) =
      if q = ⟦a⟧ then 1 else 0 := by
  classical
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hq : (⟦x⟧ : CubicOrbit N) = ⟦a⟧ ↔ x = a ∨ x = -a := CubicOrbit.mk_eq_mk_iff
  by_cases hx : x = 0
  · subst hx
    have h0 : a = 0 ↔ (⟦0⟧ : CubicOrbit N) = ⟦a⟧ := by simp [hq, eq_comm, neg_eq_zero]
    have h1 : ((1 : Multiplicative (Fin N → ZMod 3)) = ofAdd a) ↔ a = 0 := by
      rw [eq_comm, ofAdd_eq_one]
    simp only [cubicOrbitVec, Quotient.lift_mk, ↓reduceIte, OneMemClass.coe_one]
    rw [← of_one, TwistedMonoidAlgebra.repr_of, Finsupp.single_apply]
    simp only [h1, h0]
  · have hne : x ≠ -x := fun h ↦ hx (eq_zero_of_neg_eq_self h.symm)
    have hrepr (y : Fin N → ZMod 3) :
        (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).repr
            (weyl N y) (ofAdd a) = if y = a then 1 else 0 := by
      simp only [weyl_def, TwistedMonoidAlgebra.repr_of, Finsupp.single_apply,
        ofAdd.injective.eq_iff]
    have hneg : (-x = a) ↔ (x = -a) := neg_eq_iff_eq_neg
    simp only [cubicOrbitVec, Quotient.lift_mk, hx, ↓reduceIte, symmWeylFixed, symmWeyl, map_add,
      Finsupp.add_apply, hrepr, hq, hneg]
    by_cases h1 : x = a
    · have ha : a ≠ -a := h1 ▸ hne
      simp [h1, ha]
    · by_cases h2 : x = -a
      · have ha : -a ≠ a := fun h ↦ hne (by rw [h2, neg_neg, h])
        simp [h2, ha]
      · simp [h1, h2]

private theorem cubicOrbitVec_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (cubicOrbitVec N) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc q₀
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q₀
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hsum : b.coord (ofAdd a)
      ((cubicFixed N).val (∑ q : CubicOrbit N, c q • cubicOrbitVec N q)) = 0 := by
    rw [hc, map_zero, map_zero]
  rw [map_sum, map_sum] at hsum
  have hterm : ∀ q : CubicOrbit N,
      b.coord (ofAdd a) ((cubicFixed N).val (c q • cubicOrbitVec N q)) =
        c q * if q = ⟦a⟧ then 1 else 0 := fun q ↦ by
    rw [AlgHom.map_smul_of_tower, map_smul, smul_eq_mul, Module.Basis.coord_apply,
      Subalgebra.coe_val, repr_cubicOrbitVec]
  simp only [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hsum
  exact hsum

private theorem cubicOrbitVec_span (N : ℕ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (cubicOrbitVec N)) := by
  intro x _
  let S : Submodule ℂ (cubicFixed N) := Submodule.span ℂ (Set.range (cubicOrbitVec N))
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hsymm (a : Fin N → ZMod 3) : symmWeylFixed N a ∈ S := by
    by_cases ha : a = 0
    · have h0 : symmWeylFixed N 0 = (2 : ℂ) • cubicOrbitVec N ⟦0⟧ :=
        Subtype.ext (by simp [cubicOrbitVec, symmWeylFixed, symmWeyl_zero])
      rw [ha, h0]
      exact S.smul_mem (2 : ℂ) (Submodule.subset_span ⟨⟦0⟧, rfl⟩)
    · have ha' : symmWeylFixed N a = cubicOrbitVec N ⟦a⟧ :=
        Subtype.ext (by simp [cubicOrbitVec, symmWeylFixed, ha])
      rw [ha']
      exact Submodule.subset_span ⟨⟦a⟧, rfl⟩
  have h2x : (2 : ℂ) • x = (b.repr x.val).sum fun g z ↦ z • symmWeylFixed N g.toAdd := by
    apply Subtype.ext
    have hxrepr : x.val = (b.repr x.val).sum fun g z ↦ z • of g := by
      conv_lhs => rw [← b.linearCombination_repr x.val, Finsupp.linearCombination_apply]
      exact Finsupp.sum_congr fun g _ ↦ by rw [TwistedMonoidAlgebra.basis_apply]
    have hinv : x.val + cubicInversion N x.val =
        (b.repr x.val).sum fun g z ↦ z • symmWeyl N g.toAdd := by
      conv_lhs => rw [hxrepr]
      simp [symmWeyl, Finsupp.sum, map_sum, map_smul, Finset.sum_add_distrib, of_eq_weyl, smul_add]
    simpa [symmWeylFixed, SetLike.val_smul, two_smul, mem_cubicFixed.mp x.property,
      Finsupp.sum] using hinv
  have hxS : (2 : ℂ) • x ∈ S := by
    rw [h2x]
    exact S.sum_mem fun g _ ↦ S.smul_mem _ (hsymm g.toAdd)
  exact (Submodule.smul_mem_iff S two_ne_zero).mp hxS

/-- **The inversion-orbit basis of `cubicFixed N`**: `⟦0⟧ ↦ 1` and `⟦a⟧ ↦ W(a) + W(-a)` for
`a ≠ 0`. -/
noncomputable def cubicFixedBasis (N : ℕ) : Module.Basis (CubicOrbit N) ℂ (cubicFixed N) :=
  Module.Basis.mk (cubicOrbitVec_linearIndependent N) (cubicOrbitVec_span N)

@[simp] theorem cubicFixedBasis_zero (N : ℕ) : cubicFixedBasis N ⟦0⟧ = 1 :=
  Subtype.ext (by simp [cubicFixedBasis, cubicOrbitVec])

theorem coe_cubicFixedBasis_of_ne_zero {N : ℕ} {a : Fin N → ZMod 3} (ha : a ≠ 0) :
    (cubicFixedBasis N ⟦a⟧ : CubicTorus N) = weyl N a + weyl N (-a) := by
  simp only [cubicFixedBasis, Module.Basis.coe_mk, cubicOrbitVec]
  rw [Quotient.lift_mk]
  simp [ha, symmWeylFixed, symmWeyl]

/-- The `⟦a⟧`-coordinate of `x : cubicFixed N` in `cubicFixedBasis N` equals the `ofAdd a`
coordinate of `(x : CubicTorus N)` in `TwistedMonoidAlgebra.basis`. -/
theorem cubicFixedBasis_repr (N : ℕ) (x : cubicFixed N) (a : Fin N → ZMod 3) :
    (cubicFixedBasis N).repr x ⟦a⟧ =
      (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).repr
        (x : CubicTorus N) (ofAdd a) := by
  classical
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hsum : (x : CubicTorus N) =
      ∑ q : CubicOrbit N, (cubicFixedBasis N).repr x q • (cubicOrbitVec N q : CubicTorus N) := by
    conv_lhs => rw [← (cubicFixedBasis N).sum_repr x]
    simp [cubicFixedBasis]
  rw [← b.coord_apply, hsum, map_sum]
  simp [b, Module.Basis.coord_apply, repr_cubicOrbitVec]

/-- **Dimension of the inversion-fixed subalgebra**: `dim_ℂ (cubicFixed N) = (3 ^ N + 1) / 2`. -/
@[simp] theorem finrank_cubicFixed (N : ℕ) : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  classical
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  let θ : Module.End ℂ (CubicTorus N) := (cubicInversion N).toLinearMap
  let σ : Equiv.Perm (Multiplicative (Fin N → ZMod 3)) := inv_involutive.toPerm Inv.inv
  have : Module.Finite ℂ (CubicTorus N) := Module.Finite.of_basis b
  have : Module.Free ℂ (CubicTorus N) := Module.Free.of_basis b
  have hmat : _root_.LinearMap.toMatrix b b θ = σ.permMatrix ℂ := by
    ext i j
    rw [_root_.LinearMap.toMatrix_apply, TwistedMonoidAlgebra.basis_apply]
    dsimp only [θ, σ, Equiv.Perm.permMatrix]
    rw [AlgHom.toLinearMap_apply, of_eq_weyl, cubicInversion_weyl, weyl_def,
      TwistedMonoidAlgebra.repr_of, Finsupp.single_apply, PEquiv.toMatrix_apply,
      ofAdd_neg, ofAdd_toAdd]
    simp [Equiv.toPEquiv_apply, inv_eq_iff_eq_inv, eq_comm (a := i)]
  have hfix : Function.fixedPoints σ = {1} := by
    ext a
    simp only [Function.mem_fixedPoints_iff, σ, Set.mem_singleton_iff]
    exact ⟨fun h ↦ toAdd.injective (eq_zero_of_neg_eq_self (congrArg toAdd h)),
      fun h ↦ by simp [h]⟩
  have htrθ : _root_.LinearMap.trace ℂ (CubicTorus N) θ = 1 := by
    rw [_root_.LinearMap.trace_eq_matrix_trace ℂ b θ, hmat, Matrix.trace_permutation, hfix,
      Set.ncard_singleton, Nat.cast_one]
  have hneg : (-θ) ^ 2 = 1 := by ext x; simp [θ, sq]
  have hker : _root_.LinearMap.ker (1 + (-θ)) = (cubicFixed N).toSubmodule := by
    ext x
    simp only [_root_.LinearMap.mem_ker, _root_.LinearMap.add_apply, one_apply_eq_self,
      _root_.LinearMap.neg_apply, Subalgebra.mem_toSubmodule, mem_cubicFixed, θ,
      AlgHom.toLinearMap_apply]
    exact add_neg_eq_zero.trans eq_comm
  have htr := TauCeti.LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one
    (K := ℂ) (M := CubicTorus N) hneg
  rw [hker, map_neg, htrθ, sub_neg_eq_add, finrank_cubicTorus] at htr
  have hnat : 2 * Module.finrank ℂ (cubicFixed N) = 3 ^ N + 1 := by exact_mod_cast htr
  omega

/-! ### Universal property of `CubicTorus N` on site generators -/

section UniversalProperty

private def halfChainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j else 0

private theorem chainForm_eq_sub (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (ZMod 3) N a b = halfChainForm N a b - halfChainForm N b a := by
  simp only [chainForm_apply, halfChainForm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_add_left (N : ℕ) (a₁ a₂ b : Fin N → ZMod 3) :
    halfChainForm N (a₁ + a₂) b = halfChainForm N a₁ b + halfChainForm N a₂ b := by
  simp only [halfChainForm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_add_right (N : ℕ) (a b₁ b₂ : Fin N → ZMod 3) :
    halfChainForm N a (b₁ + b₂) = halfChainForm N a b₁ + halfChainForm N a b₂ := by
  simp only [halfChainForm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_single_single (N : ℕ) (i j : Fin N) (c d : ZMod 3) :
    halfChainForm N (Pi.single i c) (Pi.single j d) =
      if (i : ℕ) + 1 = j then c * d else 0 := by
  rw [halfChainForm, Fintype.sum_eq_single i (fun x hx ↦ by simp [Pi.single_eq_of_ne hx]),
    Fintype.sum_eq_single j (fun y hy ↦ by simp [Pi.single_eq_of_ne hy])]
  simp

variable {A : Type*} [Semiring A] [Algebra ℂ A]

private theorem mul_pow_of_qcomm {x y : A} {z : ZMod 3}
    (h : x * y = (cubeRootPow z : ℂ) • (y * x)) (n : ZMod 3) :
    x * y ^ n.val = (cubeRootPow (z * n) : ℂ) • (y ^ n.val * x) := by
  have hsemi : SemiconjBy x y ((cubeRootPow z : ℂ) • y) := by
    simpa [SemiconjBy, smul_mul_assoc] using h
  have hp := (hsemi.pow_right n.val).eq
  rwa [smul_pow, smul_mul_assoc, cubeRootPow_pow_val] at hp

private theorem pow_mul_of_qcomm {x y : A} {z : ZMod 3}
    (h : x * y = (cubeRootPow z : ℂ) • (y * x)) (n : ZMod 3) :
    x ^ n.val * y = (cubeRootPow (z * n) : ℂ) • (y * x ^ n.val) := by
  have hsemi : SemiconjBy y ((cubeRootPow z : ℂ) • x) x := by
    simpa [SemiconjBy, mul_smul_comm] using h.symm
  have hp := (hsemi.pow_right n.val).eq.symm
  rwa [smul_pow, mul_smul_comm, cubeRootPow_pow_val] at hp

private theorem mul_partialProd_of_qcomm :
    ∀ {N : ℕ} {u : Fin N → A} {v : A} {φ : Fin N → ZMod 3},
      (∀ i : Fin N, v * u i = (cubeRootPow (2 * φ i) : ℂ) • (u i * v)) →
      ∀ b : Fin N → ZMod 3,
        v * Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) =
          (cubeRootPow (2 * ∑ i : Fin N, φ i * b i) : ℂ) •
            (Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) * v)
  | 0, _, _, _, _, _ => by simp
  | N + 1, u, v, φ, hφ, b => by
    have ih := mul_partialProd_of_qcomm (u := u ∘ Fin.castSucc) (φ := φ ∘ Fin.castSucc)
      (fun i ↦ hφ i.castSucc) (Fin.init b)
    have hlast := mul_pow_of_qcomm (hφ (Fin.last N)) (b (Fin.last N))
    have hinit_fn : Fin.init (fun i ↦ u i ^ (b i).val) =
        fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val := by
      ext i; simp [Fin.init_def]
    rw [Fin.partialProd_last_eq_init_mul, hinit_fn, ← mul_assoc, ih, smul_mul_assoc, mul_assoc,
      hlast, mul_smul_comm, smul_smul, coe_cubeRootPow_mul, ← mul_assoc]
    congr 3; rw [Fin.sum_univ_castSucc]; simp [Fin.init, mul_add]; ring

private theorem halfChainForm_succ (N : ℕ) (b a : Fin (N + 1) → ZMod 3) :
    halfChainForm (N + 1) b a =
      halfChainForm N (Fin.init b) (Fin.init a) +
        a (Fin.last N) *
          ∑ i : Fin N, (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * b i.castSucc := by
  unfold halfChainForm
  have hlast : (∑ j : Fin (N + 1),
      if (Fin.last N : ℕ) + 1 = (j : ℕ) then b (Fin.last N) * a j else 0) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ ite_eq_right_iff.mpr fun h ↦ by simp at h; omega
  rw [Fin.sum_univ_castSucc, hlast, add_zero]
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, Finset.sum_add_distrib,
    Fin.init, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring

private theorem partialProd_mul_partialProd :
    ∀ {N : ℕ} (u : Fin N → A), (∀ j, u j ^ 3 = 1) →
      (∀ {i j : Fin N}, (i : ℕ) + 1 = j → u i * u j = (cubeRootPow 1 : ℂ) • (u j * u i)) →
      (∀ {i j : Fin N}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → u i * u j = u j * u i) →
      ∀ a b : Fin N → ZMod 3,
      Fin.partialProd (fun i ↦ u i ^ (a i).val) (Fin.last N) *
          Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) =
        (cubeRootPow (2 * halfChainForm N b a) : ℂ) •
          Fin.partialProd (fun i ↦ u i ^ ((a + b) i).val) (Fin.last N)
  | 0, _, _, _, _, _, _ => by simp [halfChainForm]
  | N + 1, u, hcube, hadj, hdist, a, b => by
    have hqcomm : ∀ i : Fin N, u (Fin.last N) * u i.castSucc =
        (cubeRootPow (2 * if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) : ℂ) •
          (u i.castSucc * u (Fin.last N)) := fun i ↦ by
      split_ifs with hi
      · have h := congrArg ((cubeRootPow 2 : ℂ) • ·) (hadj (i := i.castSucc) (j := Fin.last N) hi)
        have h3 : (2 : ZMod 3) + 1 = 0 := ZMod.natCast_self 3
        rw [smul_smul, coe_cubeRootPow_mul, h3, AddChar.map_zero_eq_one, Units.val_one,
          one_smul] at h
        simpa [mul_one] using h.symm
      · have hd : (i.castSucc : ℕ) + 2 ≤ (Fin.last N : ℕ) := by
          have := i.isLt; simp at hi ⊢; omega
        simp [hdist (Or.inr hd)]
    have hmulb := mul_partialProd_of_qcomm (u := u ∘ Fin.castSucc) hqcomm (Fin.init b)
    have hcomm := pow_mul_of_qcomm hmulb (a (Fin.last N))
    have ih := partialProd_mul_partialProd (u ∘ Fin.castSucc) (fun j ↦ hcube j.castSucc)
      (fun h ↦ hadj h) (fun h ↦ hdist h) (Fin.init a) (Fin.init b)
    have hpow : u (Fin.last N) ^ (a (Fin.last N)).val * u (Fin.last N) ^ (b (Fin.last N)).val =
        u (Fin.last N) ^ ((a + b) (Fin.last N)).val := by
      rw [← pow_add, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hcube (Fin.last N))]
    have hinit : Fin.init (a + b) = Fin.init a + Fin.init b := by ext i; simp [Fin.init_def]
    have hinit_fn (x : Fin (N + 1) → ZMod 3) :
        Fin.init (fun i ↦ u i ^ (x i).val) = fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init x i).val := by
      ext i; simp [Fin.init_def]
    set Pa := Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init a i).val) (Fin.last N)
    set Pb := Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N)
    set Ua := u (Fin.last N) ^ (a (Fin.last N)).val
    set Ub := u (Fin.last N) ^ (b (Fin.last N)).val
    have hsum :
        (2 * ∑ i : Fin N, (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * Fin.init b i) *
            a (Fin.last N) +
          2 * halfChainForm N (Fin.init b) (Fin.init a) =
          2 * halfChainForm (N + 1) b a := by
      rw [halfChainForm_succ]; simp only [Fin.init]; ring
    calc
      Fin.partialProd (fun i ↦ u i ^ (a i).val) (Fin.last (N + 1)) *
          Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last (N + 1))
        = Pa * (Ua * Pb) * Ub := by
          simp only [Fin.partialProd_last_eq_init_mul, hinit_fn, mul_assoc, Pa, Pb, Ua, Ub]
      _ = (cubeRootPow ((2 * ∑ i : Fin N,
              (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * Fin.init b i) *
            a (Fin.last N)) : ℂ) • ((Pa * Pb) * (Ua * Ub)) := by
          rw [hcomm]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = (cubeRootPow (2 * halfChainForm (N + 1) b a) : ℂ) •
            Fin.partialProd (fun i ↦ u i ^ ((a + b) i).val) (Fin.last (N + 1)) := by
          rw [ih, hpow, Fin.partialProd_last_eq_init_mul, hinit_fn, ← hinit]
          simp only [smul_mul_assoc, smul_smul, coe_cubeRootPow_mul, hsum]

/-- **Universal property of `CubicTorus N` on site generators.** Any `N` elements `u : Fin N → A` of
a `ℂ`-algebra satisfying `u j ^ 3 = 1`, `u i * u_{i+1} = ω • (u_{i+1} * u i)`, and commuting at
distance `≥ 2` determine a `ℂ`-algebra homomorphism `CubicTorus N →ₐ[ℂ] A` sending `cubicSite N j`
to `u j`. -/
noncomputable def liftSite {N : ℕ} (u : Fin N → A)
    (hcube : ∀ j, u j ^ 3 = 1)
    (hadj : ∀ {i j : Fin N}, (i : ℕ) + 1 = j → u i * u j = (cubeRootPow 1 : ℂ) • (u j * u i))
    (hdist : ∀ {i j : Fin N}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → u i * u j = u j * u i) :
    CubicTorus N →ₐ[ℂ] A :=
  TwistedMonoidAlgebra.lift
    (fun a ↦ (cubeRootPow (halfChainForm N a.toAdd a.toAdd) : ℂ) •
      Fin.partialProd (fun i ↦ u i ^ (a.toAdd i).val) (Fin.last N))
    (by simp [Fin.partialProd_one, halfChainForm])
    (fun a b ↦ by
      rw [smul_mul_smul_comm, partialProd_mul_partialProd u hcube hadj hdist]
      simp only [smul_smul, coe_cubeRootPow_mul, cubicFactor_apply]
      refine congrArg (fun z ↦ (cubeRootPow z : ℂ) • _) ?_
      simp only [chainForm_eq_sub, toAdd_mul, halfChainForm_add_left, halfChainForm_add_right]
      have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
      linear_combination (halfChainForm N b.toAdd a.toAdd - halfChainForm N a.toAdd b.toAdd) * h3)

/-- `liftSite` sends each site unitary `cubicSite N j` to `u j`. -/
@[simp] theorem liftSite_cubicSite {N : ℕ} (u : Fin N → A) (hcube) (hadj) (hdist) (j : Fin N) :
    liftSite u hcube hadj hdist (cubicSite N j) = u j := by
  rw [liftSite, cubicSite_def, weyl_def, TwistedMonoidAlgebra.lift_of, toAdd_ofAdd,
    halfChainForm_single_single]
  simp only [Nat.add_one_ne_self, ↓reduceIte, AddChar.map_zero_eq_one, Units.val_one, one_smul]
  have hsingle : (fun i ↦ u i ^ ((Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) i).val) =
      Pi.mulSingle j (u j) := by
    ext i
    by_cases hi : i = j
    · subst hi; simp [ZMod.val_one]
    · simp [Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
  rw [hsingle, Fin.partialProd_mulSingle]

end UniversalProperty

/-- The site unitaries `cubicSite N` generate `CubicTorus N` as a `ℂ`-algebra. -/
theorem adjoin_range_cubicSite (N : ℕ) :
    Algebra.adjoin ℂ (Set.range (cubicSite N)) = ⊤ := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicSite N))
  have hsingle (j : Fin N) (r : ZMod 3) : weyl N (Pi.single j r) ∈ S := by
    have hj : cubicSite N j ∈ S := Algebra.subset_adjoin (Set.mem_range_self j)
    rcases ZMod.eq_zero_or_eq_one_or_eq_two r with rfl | rfl | rfl
    · rw [Pi.single_zero, weyl_zero]; exact S.one_mem
    · rwa [← cubicSite_def]
    · have h2 : (2 : ZMod 3) = ((2 : ℕ) : ZMod 3) := Nat.cast_ofNat.symm
      rw [h2, ← cubicSite_pow j 2]
      exact S.pow_mem hj 2
  have hweyl (a : Fin N → ZMod 3) : weyl N a ∈ S := by
    have hsum : a = ∑ j : Fin N, Pi.single j (a j) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    induction (Finset.univ : Finset (Fin N)) using Finset.cons_induction with
    | empty => simp [S.one_mem]
    | cons j s _ ih =>
      rw [Finset.sum_cons]
      set u : Fin N → ZMod 3 := Pi.single j (a j)
      set v : Fin N → ZMod 3 := ∑ i ∈ s, Pi.single i (a i)
      have hmul := S.smul_mem (S.mul_mem (hsingle j (a j)) ih)
        ((cubeRootPow (-(2 * chainForm (ZMod 3) N u v)) : ℂˣ) : ℂ)
      rwa [weyl_mul_weyl, smul_smul, ← Units.val_mul, ← AddChar.map_add_eq_mul,
        neg_add_cancel, AddChar.map_zero_eq_one, Units.val_one, one_smul] at hmul
  suffices ∀ x : CubicTorus N, x ∈ S from eq_top_iff.mpr fun x _ ↦ this x
  intro x
  induction (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
      (cubicFactor N)).mem_span x using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [TwistedMonoidAlgebra.basis_apply, of_eq_weyl]; exact hweyl a.toAdd
  | zero => exact S.zero_mem
  | add _ _ _ _ hx hy => exact S.add_mem hx hy
  | smul _ _ _ hx => exact S.smul_mem hx _

/-- Two `ℂ`-algebra homomorphisms out of `CubicTorus N` agreeing on `cubicSite N` are equal. -/
theorem algHom_ext_cubicSite {N : ℕ} {A : Type*} [Semiring A] [Algebra ℂ A]
    {F G : CubicTorus N →ₐ[ℂ] A} (h : ∀ j : Fin N, F (cubicSite N j) = G (cubicSite N j)) :
    F = G :=
  AlgHom.ext_of_adjoin_eq_top (adjoin_range_cubicSite N) (by rintro _ ⟨j, rfl⟩; exact h j)

/-! ### Generation of `cubicFixed N` by `cubicProjection N` and surjectivity of `cubicHom` -/

private theorem symmWeyl_mul_symmWeyl (N : ℕ) (a b : Fin N → ZMod 3) :
    symmWeyl N a * symmWeyl N b =
      (cubeRootPow (2 * chainForm (ZMod 3) N a b) : ℂ) • symmWeyl N (a + b) +
        (cubeRootPow (-(2 * chainForm (ZMod 3) N a b)) : ℂ) • symmWeyl N (a - b) := by
  have h1 : -a + -b = -(a + b) := by ring
  have h2 : -a + b = -(a - b) := by ring
  simp only [symmWeyl, add_mul, mul_add, weyl_mul_weyl, map_neg, LinearMap.neg_apply,
    mul_neg, neg_neg, h1, h2, ← sub_eq_add_neg, smul_add]
  abel

private theorem symmWeyl_add_mem_of_chainForm_ne_zero {N : ℕ} {S : Subalgebra ℂ (CubicTorus N)}
    {a b : Fin N → ZMod 3} (ha : symmWeyl N a ∈ S) (hb : symmWeyl N b ∈ S)
    (hc : chainForm (ZMod 3) N a b ≠ 0) :
    symmWeyl N (a + b) ∈ S := by
  set αu : ℂˣ := cubeRootPow (2 * chainForm (ZMod 3) N a b)
  set α : ℂ := (αu : ℂ)
  set β : ℂ := ((αu⁻¹ : ℂˣ) : ℂ)
  have hαβ : α * β = 1 := by simp [α, β]
  have hβα : β * α = 1 := mul_comm α β ▸ hαβ
  have hα3 : α ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one, Units.val_one]
  have hα1 : α ≠ 1 := fun h1 ↦ by
    have hu : αu = 1 := Units.ext h1
    rw [cubeRootPow_eq_one_iff] at hu
    exact hc ((mul_eq_zero.mp hu).resolve_left (by decide))
  have hab : symmWeyl N a * symmWeyl N b = α • symmWeyl N (a + b) + β • symmWeyl N (a - b) := by
    simp only [symmWeyl_mul_symmWeyl, AddChar.map_neg_eq_inv, α, β, αu]
  have hba : symmWeyl N b * symmWeyl N a = β • symmWeyl N (a + b) + α • symmWeyl N (a - b) := by
    have hsw : 2 * chainForm (ZMod 3) N b a = -(2 * chainForm (ZMod 3) N a b) := by
      rw [chainForm_swap]; ring
    rw [symmWeyl_mul_symmWeyl, hsw, AddChar.map_neg_eq_inv, neg_neg, add_comm b a,
      ← neg_sub a b, symmWeyl_neg]
  have hcomb : α • (symmWeyl N a * symmWeyl N b) + (-β) • (symmWeyl N b * symmWeyl N a) =
      (α ^ 2 - β ^ 2) • symmWeyl N (a + b) := by
    rw [hab, hba]
    module
  have hne : α ^ 2 - β ^ 2 ≠ 0 := fun h0 ↦ hα1 <| sub_eq_zero.mp <| by
    linear_combination (α ^ 2) * h0 - α * hα3 + (β * α + 1) * hβα
  exact (Submodule.smul_mem_iff S.toSubmodule hne).mp
    (hcomb ▸ S.add_mem (S.smul_mem (S.mul_mem ha hb) α) (S.smul_mem (S.mul_mem hb ha) (-β)))

private theorem symmWeyl_single_mem_adjoin (N : ℕ) (j : Fin N) (r : ZMod 3) :
    symmWeyl N (Pi.single j r) ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  have hp : symmWeyl N (Pi.single j 1) ∈ S := by
    have h1 : (1 : CubicTorus N) + (-1 : ℂ) • (1 : CubicTorus N) = 0 := by
      nth_rw 1 [← one_smul ℂ (1 : CubicTorus N)]
      rw [← add_smul, add_neg_cancel, zero_smul]
    have heq : symmWeyl N (Pi.single j 1) =
        (3 : ℂ) • cubicProjection N j + (-1 : ℂ) • (1 : CubicTorus N) := by
      rw [symmWeyl, ← cubicSite_def, ← cubicSite_sq_eq_weyl_neg_single,
        cubicProjection_def, smul_smul, mul_inv_cancel₀ (by norm_num), one_smul,
        add_right_comm (1 + cubicSite N j), add_right_comm 1 (cubicSite N j), h1, zero_add]
    exact heq ▸ S.add_mem (S.smul_mem (Algebra.subset_adjoin (Set.mem_range_self j)) (3 : ℂ))
      (S.smul_mem S.one_mem (-1 : ℂ))
  rcases ZMod.eq_zero_or_eq_one_or_eq_two r with rfl | rfl | rfl
  · rw [Pi.single_zero, symmWeyl_zero]; exact S.smul_mem S.one_mem (2 : ℂ)
  · exact hp
  · have hneg1 : (-1 : ZMod 3) = 2 := by decide
    simpa [← hneg1, Pi.single_neg, symmWeyl_neg] using hp

private theorem chainForm_prefix_single {N m : ℕ} (hm : m + 1 < N)
    {y : Fin N → ZMod 3} (hy : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → y i = 0) (r : ZMod 3) :
    chainForm (ZMod 3) N y (Pi.single ⟨m + 1, hm⟩ r) = y ⟨m, by omega⟩ * r := by
  rw [chainForm_apply, Fintype.sum_eq_single (⟨m, by omega⟩ : Fin N)]
  · rw [Fintype.sum_eq_single (⟨m + 1, hm⟩ : Fin N)]
    · simp
    · intro j hj
      have hne : ¬ (m : ℕ) + 1 = (j : ℕ) := fun h ↦ hj (Fin.ext h.symm)
      simp [hne]
  · intro i hi
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    split_ifs with hij
    · have hj : j ≠ ⟨m + 1, hm⟩ := fun h ↦
        hi (Fin.ext (by have := congrArg Fin.val h; simp at this ⊢; omega))
      by_cases him : i = ⟨m + 1, hm⟩
      · subst him; simp [Pi.single_eq_of_ne hj, hy j (by simp at hij; omega)]
      · simp [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne him]
    · rfl

/-- Inductive elimination step for `symmWeyl_mem_adjoin_of_support`. -/
private theorem symmWeyl_add_single_mem_adjoin_of_prefix {N m : ℕ} (hm : m + 1 < N)
    (ih : ∀ z : Fin N → ZMod 3, (∀ i : Fin N, m + 1 ≤ (i : ℕ) → z i = 0) →
      symmWeyl N z ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)))
    {y : Fin N → ZMod 3} (hy : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → y i = 0)
    {r : ZMod 3} (hr : r ≠ 0) :
    symmWeyl N (y + Pi.single ⟨m + 1, hm⟩ r) ∈
      Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  let jk : Fin N := ⟨m + 1, hm⟩
  let jm : Fin N := ⟨m, by omega⟩
  have hstep : ∀ (z : Fin N → ZMod 3) (s : ZMod 3),
      (∀ i : Fin N, m + 1 ≤ (i : ℕ) → z i = 0) → z jm ≠ 0 → s ≠ 0 →
      symmWeyl N (z + Pi.single jk s) ∈ S := fun z s hz hzm hs ↦
    symmWeyl_add_mem_of_chainForm_ne_zero (ih z hz) (symmWeyl_single_mem_adjoin N jk s)
      (by rw [chainForm_prefix_single hm hz]; exact mul_ne_zero hzm hs)
  by_cases hym : y jm = 0
  · let em : Fin N → ZMod 3 := Pi.single jm 1
    let b := y + em
    let c := -em + Pi.single jk r
    let y' := y + Pi.single jm 2
    have hbc : b + c = y + Pi.single jk r := by simp [b, c, add_assoc]
    have hbcinv : b - c = y' + Pi.single jk (-r) := by
      ext i; simp [b, c, y', em, Pi.single_apply]; split_ifs <;> ring
    have hne_jm : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → i ≠ jm := fun i hi h ↦ by subst h; simp [jm] at hi
    have hb_mem : symmWeyl N b ∈ S := ih b fun i hi ↦ by
      simp [b, em, Pi.single_eq_of_ne (hne_jm i hi), hy i hi]
    have hc_mem : symmWeyl N c ∈ S :=
      hstep (-em) r (fun i hi ↦ by simp [em, Pi.single_eq_of_ne (hne_jm i hi)]) (by simp [em]) hr
    have hy'_mem : symmWeyl N (b - c) ∈ S :=
      hbcinv ▸ hstep y' (-r) (fun i hi ↦ by simp [y', Pi.single_eq_of_ne (hne_jm i hi), hy i hi])
        (by simp only [y', Pi.add_apply, hym, zero_add, Pi.single_eq_same, ne_eq]; decide)
        (neg_ne_zero.mpr hr)
    set α : ℂ := (cubeRootPow (2 * chainForm (ZMod 3) N b c) : ℂ)
    set γ : ℂ := (cubeRootPow (-(2 * chainForm (ZMod 3) N b c)) : ℂ)
    have hαγ : γ * α = 1 := by
      simp [α, γ, coe_cubeRootPow_mul]
    have hcomb : symmWeyl N b * symmWeyl N c + (-γ) • symmWeyl N (b - c) =
        α • symmWeyl N (y + Pi.single jk r) := by
      rw [symmWeyl_mul_symmWeyl N b c, hbc, add_assoc, ← add_smul, add_neg_cancel, zero_smul,
        add_zero]
    have hres := S.smul_mem
      (hcomb ▸ S.add_mem (S.mul_mem hb_mem hc_mem) (S.smul_mem hy'_mem (-γ))) γ
    rwa [smul_smul, hαγ, one_smul] at hres
  · exact hstep y r hy hym hr

private theorem symmWeyl_mem_adjoin_of_support (N k : ℕ) :
    ∀ (a : Fin N → ZMod 3), (∀ i : Fin N, k ≤ (i : ℕ) → a i = 0) →
      symmWeyl N a ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  induction k with
  | zero =>
    intro a ha
    have ha0 : a = 0 := funext fun i ↦ ha i (Nat.zero_le _)
    rw [ha0, symmWeyl_zero]
    exact (Algebra.adjoin ℂ (Set.range (cubicProjection N))).smul_mem (Subalgebra.one_mem _) (2 : ℂ)
  | succ k ih =>
    intro a ha
    by_cases hkN : k < N
    · let jk : Fin N := ⟨k, hkN⟩
      set r := a jk
      by_cases hr : r = 0
      · refine ih a fun i hi ↦ ?_
        rcases eq_or_lt_of_le hi with hval | hlt
        · exact (Fin.ext hval.symm : i = jk) ▸ hr
        · exact ha i hlt
      · let d : Fin N → ZMod 3 := Pi.single jk r
        let y : Fin N → ZMod 3 := a - d
        have hy : ∀ i : Fin N, k ≤ (i : ℕ) → y i = 0 := fun i hi ↦ by
          rcases eq_or_lt_of_le hi with hval | hlt
          · have hij : i = jk := Fin.ext hval.symm; subst hij; simp [y, d, r]
          · have hne : i ≠ jk := fun h ↦ by subst h; exact Nat.lt_irrefl _ hlt
            simp [y, d, Pi.single_eq_of_ne hne, ha i hlt]
        have hay : a = y + d := (sub_add_cancel a d).symm
        rw [hay]
        rcases k with _ | m
        · have hy0 : y = 0 := funext fun i ↦ hy i (Nat.zero_le _)
          rw [hy0, zero_add]
          exact symmWeyl_single_mem_adjoin N jk r
        · exact symmWeyl_add_single_mem_adjoin_of_prefix hkN ih hy hr
    · exact ih a fun i _ ↦ absurd i.isLt (by omega)

/-- **The projections `cubicProjection N` generate `cubicFixed N`** as a `ℂ`-algebra. -/
theorem adjoin_range_cubicProjection (N : ℕ) :
    Algebra.adjoin ℂ (Set.range (cubicProjection N)) = cubicFixed N := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  refine le_antisymm (Algebra.adjoin_le_iff.mpr <| by
    rintro _ ⟨j, rfl⟩; exact cubicProjection_mem_cubicFixed j) fun x hx ↦ ?_
  have hsymm : ∀ z : CubicTorus N, z + cubicInversion N z ∈ S := fun z ↦ by
    induction (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).mem_span z using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨a, rfl⟩ := hw
      rw [TwistedMonoidAlgebra.basis_apply, of_eq_weyl, cubicInversion_weyl]
      exact symmWeyl_mem_adjoin_of_support N N a.toAdd fun i hi ↦ absurd i.isLt (not_lt.mpr hi)
    | zero => simp [S.zero_mem]
    | add _ _ _ _ hy hw => rw [map_add, add_add_add_comm]; exact S.add_mem hy hw
    | smul c _ _ hy => rw [map_smul, ← smul_add]; exact S.smul_mem hy c
  have hx2 := hsymm x
  rw [mem_cubicFixed.mp hx, ← two_smul ℂ x] at hx2
  exact (Submodule.smul_mem_iff S.toSubmodule two_ne_zero).mp hx2

/-- **Surjectivity of `cubicHom`.** For every `m : ℕ`, the comparison homomorphism
`TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` is surjective. -/
theorem cubicHom_surjective (m : ℕ) : Function.Surjective (cubicHom m) := by
  let Φ : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).val.comp (cubicHom m)
  have hrange : Φ.range = cubicFixed (m - 1) := by
    rw [← Algebra.map_top, ← adjoin_range_e, AlgHom.map_adjoin, ← Set.range_comp]
    let S₁ := Algebra.adjoin ℂ (Set.range (Φ ∘ e (Real.sqrt 3 : ℂ)))
    let S₂ := Algebra.adjoin ℂ (Set.range (cubicProjection (m - 1)))
    have hadj : S₁ = S₂ := le_antisymm
      (Algebra.adjoin_le_iff.mpr <| by
        rintro _ ⟨j, rfl⟩
        simpa [Φ, coe_cubicHom_e] using
          S₂.smul_mem (Algebra.subset_adjoin (Set.mem_range_self j)) (Real.sqrt 3 : ℂ))
      (Algebra.adjoin_le_iff.mpr <| by
        rintro _ ⟨j, rfl⟩
        have hj0 : (Φ ∘ e (Real.sqrt 3 : ℂ)) j ∈ S₁ :=
          Algebra.subset_adjoin (Set.mem_range_self j)
        simp only [Function.comp_apply, Φ, AlgHom.comp_apply, Subalgebra.coe_val,
          coe_cubicHom_e] at hj0
        exact (Submodule.smul_mem_iff S₁.toSubmodule sqrt_three_ne_zero).mp hj0)
    exact hadj.trans (adjoin_range_cubicProjection (m - 1))
  intro y
  obtain ⟨x, hx⟩ : (y : CubicTorus (m - 1)) ∈ Φ.range := hrange.symm ▸ y.property
  exact ⟨x, Subtype.ext hx⟩

end TauCeti.TemperleyLieb
