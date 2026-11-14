/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded

/-!
# Morphisms of ungraded `A∞` right modules

Let `M` and `M'` be ungraded `A∞` right modules (`TauCeti.UngradedAInfinityRightModule`) over an
algebra `A` with a linear map `d`, with operations `m_{n+1}` and `m'_{n+1}`. A **morphism**
`f : M → M'` is a family of maps `f_{n+1} : M ⊗ A^{⊗ n} → M'`, here
`map n : MultilinearMap (RingHom.id R) (Fin n → A) (M →ₗ[R] M')`, satisfying for every
`m` and `a₁, …, aₙ`

`∑_{i + j = n} f_{j+1}(m_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
`  + ∑_{i + j = n} m'_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
`  + ∑_l f_{n+1}(m, a₁, …, d aₗ, …, aₙ) + ∑_l f_n(m, a₁, …, aₗ aₗ₊₁, …, aₙ) = 0`

(`TauCeti.UngradedAInfinityRightModuleHom`). Over a ring of characteristic two these are the
relations of an `A∞` morphism, as in Lipshitz, Ozsváth and Thurston (§2.1): every Koszul sign
is `1`. Their length-zero case says that `f₁` is a chain map for `m₁` and `m'₁`. These are the
morphisms of type `A` modules of bordered Heegaard Floer homology, which induce chain maps of box
tensor products (`TauCeti.LowDimTopology.Bordered.TypeA`). Tau Ceti's morphisms of graded `A∞`
modules (`TauCeti.AInfinityRightModuleHom`) do not apply here, since the modules are ungraded.

* **Mapping cones.** The relations of a morphism make the operations
  `(m, m') ↦ (m_{n+1}(m, a…), m'_{n+1}(m', a…) + f_{n+1}(m, a…))` on `M × M'` satisfy the `A∞`
  relations (`TauCeti.UngradedAInfinityRightModuleHom.cone`). This turns statements about
  morphisms into statements about modules: the box tensor differential of the cone squares to
  zero, and its off-diagonal component is the map induced by `f`.
* **Strict morphisms.** Over a ring of characteristic two, a linear map `L` commuting with all the
  operations is a morphism with `f₁ = L` and `f_{n+1} = 0` for `n ≥ 1`
  (`TauCeti.UngradedAInfinityRightModuleHom.ofLinearMap`). This gives the identity morphism
  (`TauCeti.UngradedAInfinityRightModuleHom.id`), and makes an `A`-linear chain map of differential
  right modules a morphism of the associated `A∞` modules
  (`TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModuleHom`).

## Main definitions

* `TauCeti.UngradedAInfinityRightModuleHom`: a morphism of ungraded `A∞` right modules.
* `TauCeti.UngradedAInfinityRightModuleHom.cone`: its mapping cone.
* `TauCeti.UngradedAInfinityRightModuleHom.ofLinearMap`: the strict morphism of a linear map
  commuting with the operations.
* `TauCeti.UngradedAInfinityRightModuleHom.id`: the identity morphism.
* `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModuleHom`: an `A`-linear chain map of
  differential modules as a morphism of `A∞` modules.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.1 (morphisms of `A∞` modules over `𝔽₂`).
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology Homotopy Appl. **3**
  (2001), 1–35, Section 4 (morphisms of `A∞` modules).
-/

public section

open Finset

namespace TauCeti

variable {R A M M' : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {d : A →ₗ[R] A}

/-- A **morphism of ungraded `A∞` right modules** from `M` to `M'`. The component `map n` is
`f_{n+1} : M ⊗ A^{⊗ n} → M'`, and the components satisfy the relation of every length `n`: the
terms `f_{j+1}(m_{i+1}(m, …), …)` and `m'_{j+1}(f_{i+1}(m, …), …)` for `i + j = n`, the differential
terms `TauCeti.ungradedStasheffDiff` and the product terms `TauCeti.ungradedStasheffMul` of the
family `f` sum to zero. As for `TauCeti.UngradedAInfinityRightModule`, no sign appears: over a ring
of characteristic two these are the relations of an `A∞` morphism. -/
@[ext]
structure UngradedAInfinityRightModuleHom (Mm : UngradedAInfinityRightModule d M)
    (Mm' : UngradedAInfinityRightModule d M') where
  /-- The component `f_{n+1}`, with `n` algebra inputs. -/
  map : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')
  /-- The relation of length `n`. -/
  stasheff (n : ℕ) (a : Fin n → A) (m : M) :
    ∑ k : Fin (n + 1), map (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (Mm.act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ∑ k : Fin (n + 1), Mm'.act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (map k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ungradedStasheffDiff map d n a m + ungradedStasheffMul map n a m = 0

namespace UngradedAInfinityRightModuleHom

variable {Mm : UngradedAInfinityRightModule d M} {Mm' : UngradedAInfinityRightModule d M'}
  (f : UngradedAInfinityRightModuleHom Mm Mm')

/-! ### The mapping cone -/

/-- The operations of the mapping cone of `f`:
`(m, m') ↦ (m_{n+1}(m, a…), m'_{n+1}(m', a…) + f_{n+1}(m, a…))`. -/
private noncomputable def coneAct (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M × M' →ₗ[R] M × M') where
  toFun a := (Mm.act n a).prodMap (Mm'.act n a) +
    LinearMap.inr R M M' ∘ₗ f.map n a ∘ₗ LinearMap.fst R M M'
  map_update_add' a i x y := by
    ext <;> simp [MultilinearMap.map_update_add]
  map_update_smul' a i c x := by
    ext <;> simp [MultilinearMap.map_update_smul]

private theorem coneAct_apply (n : ℕ) (a : Fin n → A) (p : M × M') :
    f.coneAct n a p = (Mm.act n a p.1, Mm'.act n a p.2 + f.map n a p.1) := by
  simp [coneAct]

private theorem stasheffComp_coneAct (n : ℕ) (a : Fin n → A) (p : M × M') :
    ungradedStasheffComp f.coneAct n a p =
      (ungradedStasheffComp Mm.act n a p.1, ungradedStasheffComp Mm'.act n a p.2 +
        (∑ k : Fin (n + 1), f.map (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
          (Mm.act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) p.1) +
        ∑ k : Fin (n + 1), Mm'.act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
          (f.map k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) p.1))) := by
  refine Prod.ext ?_ ?_ <;> simp only [ungradedStasheffComp_def, coneAct_apply, Prod.fst_sum,
    Prod.snd_sum, map_add, sum_add_distrib]
  abel

private theorem stasheffDiff_coneAct (n : ℕ) (a : Fin n → A) (p : M × M') :
    ungradedStasheffDiff f.coneAct d n a p =
      (ungradedStasheffDiff Mm.act d n a p.1,
        ungradedStasheffDiff Mm'.act d n a p.2 + ungradedStasheffDiff f.map d n a p.1) := by
  refine Prod.ext ?_ ?_ <;>
    simp [ungradedStasheffDiff_def, coneAct_apply, Prod.fst_sum, Prod.snd_sum, sum_add_distrib]

private theorem stasheffMul_coneAct (n : ℕ) (a : Fin n → A) (p : M × M') :
    ungradedStasheffMul f.coneAct n a p =
      (ungradedStasheffMul Mm.act n a p.1,
        ungradedStasheffMul Mm'.act n a p.2 + ungradedStasheffMul f.map n a p.1) := by
  cases n with
  | zero => simp [Prod.zero_eq_mk]
  | succ n =>
    refine Prod.ext ?_ ?_ <;>
      simp [ungradedStasheffMul_succ, coneAct_apply, Prod.fst_sum, Prod.snd_sum, sum_add_distrib]

/-- The **mapping cone** of a morphism `f : M → M'`: the `A∞` module on `M × M'` with operations
`(m, m') ↦ (m_{n+1}(m, a…), m'_{n+1}(m', a…) + f_{n+1}(m, a…))`. Its relation of length `n` is
the relation of `M` on the first component, and on the second the sum of the relations of `M'` and
of `f`. -/
noncomputable def cone : UngradedAInfinityRightModule d (M × M') where
  act := f.coneAct
  stasheff n a p := by
    rw [stasheffComp_coneAct, stasheffDiff_coneAct, stasheffMul_coneAct]
    refine Prod.ext (Mm.stasheff n a p.1) ?_
    simp only [Prod.snd_add, Prod.snd_zero]
    have h := congrArg₂ (· + ·) (Mm'.stasheff n a p.2) (f.stasheff n a p.1)
    rw [add_zero] at h
    rw [← h]
    abel

@[simp]
theorem cone_act_apply (n : ℕ) (a : Fin n → A) (p : M × M') :
    f.cone.act n a p = (Mm.act n a p.1, Mm'.act n a p.2 + f.map n a p.1) :=
  f.coneAct_apply n a p

/-- The operation `m_{n+1}` of the mapping cone vanishes when those of `M`, `M'` and `f` do. -/
theorem cone_act_eq_zero {n : ℕ} (h : Mm.act n = 0) (h' : Mm'.act n = 0) (hf : f.map n = 0) :
    f.cone.act n = 0 :=
  MultilinearMap.ext fun a => LinearMap.ext fun p => by simp [h, h', hf]

/-- **The matrix module of the mapping cone.** On row vectors `ψ : X → M × M'`, the operations of
the matrix module of the cone have first component the operations of the matrix module of `M` on
the first components of `ψ`, and second component those of the matrix module of `M'` on the second
components, plus the sum over the paths `x₀ → ⋯ → xₙ = z` of `f_{n+1}(ψ x₀, F₁ x₀ x₁, …)`. -/
theorem matrixAct_cone_apply (X : Type*) [Fintype X] [DecidableEq X] (n : ℕ)
    (F : Fin n → Matrix X X A) (ψ : X → M × M') (z : X) :
    f.cone.matrixAct X n F ψ z =
      (Mm.matrixAct X n F (fun x => (ψ x).1) z, Mm'.matrixAct X n F (fun x => (ψ x).2) z +
        ∑ x : Fin (n + 1) → X, if x (Fin.last n) = z then
          f.map n (fun l => F l (x l.castSucc) (x l.succ)) (ψ (x 0)).1 else 0) := by
  simp only [UngradedAInfinityRightModule.matrixAct_apply]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    exact sum_congr rfl fun x _ => by split_ifs <;> simp
  · rw [Prod.snd_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-! ### Strict morphisms -/

/-- The components of a strict morphism: `f₁ = L` and `f_{n+1} = 0` for `n ≥ 1`. -/
private noncomputable def strictMap (L : M →ₗ[R] M') :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) _ L
  | _ + 1 => 0

private theorem strictMap_apply_of_eq_zero (L : M →ₗ[R] M') {n : ℕ} (hn : n = 0) (a : Fin n → A)
    (m : M) : strictMap L n a m = L m := by
  subst hn
  rfl

private theorem strictMap_eq_zero (L : M →ₗ[R] M') {n : ℕ} (hn : n ≠ 0) :
    strictMap (A := A) L n = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rfl

variable (Mm Mm') in
/-- A **strict morphism**: over a ring of characteristic two, a linear map `L` commuting with all
the operations, `L (m_{n+1}(m, a…)) = m'_{n+1}(L m, a…)`, is a morphism with `f₁ = L` and
`f_{n+1} = 0` for `n ≥ 1`. -/
noncomputable def ofLinearMap [CharP R 2] (L : M →ₗ[R] M')
    (hL : ∀ n a m, L (Mm.act n a m) = Mm'.act n a (L m)) :
    UngradedAInfinityRightModuleHom Mm Mm' where
  map := strictMap L
  stasheff n a m := by
    -- Only `f₁` contributes: to the first sum at `i = n`, and to the second at `i = 0`.
    have h₁ : ∑ k : Fin (n + 1), strictMap L (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (Mm.act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) =
          L (Mm.act n a m) := by
      rw [sum_eq_single (Fin.last n) (fun k _ hk => by
        rw [strictMap_eq_zero L (by have := Fin.val_lt_last hk; omega), zero_apply,
          LinearMap.zero_apply]) (by simp), strictMap_apply_of_eq_zero L (by simp)]
      rfl
    have h₂ : ∑ k : Fin (n + 1), Mm'.act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (strictMap L k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) =
          Mm'.act n a (L m) := by
      rw [sum_eq_single 0 (fun k _ hk => by
        rw [strictMap_eq_zero L (Fin.val_ne_zero_iff.mpr hk), zero_apply,
          LinearMap.zero_apply, map_zero]) (by simp)]
      rw [strictMap_apply_of_eq_zero L (Fin.val_zero (n + 1))]
      simp only [Fin.val_zero, zero_add, Fin.eta]
      -- The arity `n - 0` is `n` by definition.
      rfl
    have hdiff : ungradedStasheffDiff (strictMap L) d n a m = 0 := by
      cases n with
      | zero => simp [ungradedStasheffDiff_def]
      | succ n => simp [ungradedStasheffDiff_def, strictMap_eq_zero]
    have hmul : ungradedStasheffMul (strictMap L) n a m = 0 := by
      rcases n with _ | _ | n
      · simp
      · simp [ungradedStasheffMul_succ]
      · simp [ungradedStasheffMul_succ, strictMap_eq_zero]
    rw [h₁, h₂, hdiff, hmul, hL, add_zero, add_zero, add_self_eq_zero_of_charTwo R]

@[simp]
theorem ofLinearMap_map_zero [CharP R 2] (L : M →ₗ[R] M')
    (hL : ∀ n a m, L (Mm.act n a m) = Mm'.act n a (L m)) (a : Fin 0 → A) (m : M) :
    (ofLinearMap Mm Mm' L hL).map 0 a m = L m :=
  (rfl)

@[simp]
theorem ofLinearMap_map_add_one [CharP R 2] (L : M →ₗ[R] M')
    (hL : ∀ n a m, L (Mm.act n a m) = Mm'.act n a (L m)) (n : ℕ) :
    (ofLinearMap Mm Mm' L hL).map (n + 1) = 0 :=
  (rfl)

variable (Mm) in
/-- The **identity morphism** of an `A∞` module, over a ring of characteristic two: `f₁ = id` and
`f_{n+1} = 0` for `n ≥ 1`. -/
noncomputable def id [CharP R 2] : UngradedAInfinityRightModuleHom Mm Mm :=
  ofLinearMap Mm Mm LinearMap.id fun _ _ _ => rfl

@[simp]
theorem id_map_zero [CharP R 2] (a : Fin 0 → A) (m : M) : (id Mm).map 0 a m = m :=
  (rfl)

@[simp]
theorem id_map_add_one [CharP R 2] (n : ℕ) : (id Mm).map (n + 1) = 0 :=
  (rfl)

end UngradedAInfinityRightModuleHom

/-! ### Differential modules -/

namespace IsUngradedDGRightModule

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [Module Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M']
  {dM : M →ₗ[R] M} {dM' : M' →ₗ[R] M'}

/-- **Chain maps of differential modules are `A∞` morphisms.** Over a ring of characteristic two,
an `A`-linear map `g` of differential right modules commuting with the differentials is a strict
morphism of the associated `A∞` modules, with `f₁ = g` and `f_{n+1} = 0` for `n ≥ 1`. -/
noncomputable def toUngradedAInfinityRightModuleHom [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) (hM' : IsUngradedDGRightModule d dM')
    (g : M →ₗ[Aᵐᵒᵖ] M') (hg : ∀ m, g (dM m) = dM' (g m)) :
    UngradedAInfinityRightModuleHom hM.toUngradedAInfinityRightModule
      hM'.toUngradedAInfinityRightModule :=
  .ofLinearMap _ _ (g.restrictScalars R) fun n a m => by
    rcases n with _ | _ | n
    · simp [hg]
    · simp
    · simp

@[simp]
theorem toUngradedAInfinityRightModuleHom_map_zero [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) (hM' : IsUngradedDGRightModule d dM')
    (g : M →ₗ[Aᵐᵒᵖ] M') (hg : ∀ m, g (dM m) = dM' (g m)) (a : Fin 0 → A) (m : M) :
    (toUngradedAInfinityRightModuleHom hM hM' g hg).map 0 a m = g m :=
  (rfl)

@[simp]
theorem toUngradedAInfinityRightModuleHom_map_add_one [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) (hM' : IsUngradedDGRightModule d dM')
    (g : M →ₗ[Aᵐᵒᵖ] M') (hg : ∀ m, g (dM m) = dM' (g m)) (n : ℕ) :
    (toUngradedAInfinityRightModuleHom hM hM' g hg).map (n + 1) = 0 :=
  (rfl)

end IsUngradedDGRightModule

end TauCeti
