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
* **Composition.** Over a ring of characteristic two, morphisms `f : M → M'` and `g : M' → M''`
  compose to the morphism with components
  `(g ∘ f)_{n+1}(m, a…) = ∑_{i + j = n} g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
  (`TauCeti.UngradedAInfinityRightModuleHom.comp`). In the relation of `g ∘ f`, the terms
  `g_{k+1}(m'_{j+1}(f_{i+1}(m, …), …), …)` arise twice, once from the relation of `f` and once
  from that of `g`, and cancel. Composition is associative, with the identity morphism as a
  two-sided unit. On box tensor products with a type `D` structure the composite induces the
  composite map; see `TauCeti.LowDimTopology.Bordered.TypeA.Composition`.

## Main definitions

* `TauCeti.UngradedAInfinityRightModuleHom`: a morphism of ungraded `A∞` right modules.
* `TauCeti.UngradedAInfinityRightModuleHom.cone`: its mapping cone.
* `TauCeti.UngradedAInfinityRightModuleHom.ofLinearMap`: the strict morphism of a linear map
  commuting with the operations.
* `TauCeti.UngradedAInfinityRightModuleHom.id`: the identity morphism.
* `TauCeti.UngradedAInfinityRightModuleHom.comp`: the composite of two morphisms.
* `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModuleHom`: an `A`-linear chain map of
  differential modules as a morphism of `A∞` modules.

## Main results

* `TauCeti.UngradedAInfinityRightModuleHom.comp_map_apply`: the components of a composite.
* `TauCeti.UngradedAInfinityRightModuleHom.comp_assoc`,
  `TauCeti.UngradedAInfinityRightModuleHom.id_comp`,
  `TauCeti.UngradedAInfinityRightModuleHom.comp_id`: composition is associative and unital.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.1 (morphisms of `A∞` modules over `𝔽₂` and their composition).
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

/-! ### Composition -/

section Composition

/-! The relation of a composite `g ∘ f` is proved for the families of components, the maps
`(n : ℕ) → (Fin n → A) → (M →ₗ[R] M')` underlying morphisms and operations. The composite of two
families is `(F ⋆ G)_{n+1}(m, a…) = ∑_{i + j = n} F_{j+1}(G_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`, so
that the composite terms of the relation of `f` are `f ⋆ m + m' ⋆ f`. This product is associative,
and the differential terms and the product terms of the relations are derivations for it. Hence the
relations of `f` and `g` give those of `g ⋆ f`, the two cross terms `g ⋆ m' ⋆ f` cancelling in
characteristic two. The computations read a tuple `a : Fin n → A` as the segment `[0, n)` of a
sequence `b : ℕ → A`, so that the arities of the components are natural numbers rather than
dependent bounds. -/

variable {M'' N : Type*} [AddCommGroup M''] [Module R M''] [AddCommGroup N] [Module R N]
  {Mm'' : UngradedAInfinityRightModule d M''}

/-- The segment `(b s, …, b (s + k - 1))` of a sequence. -/
private def seg {α : Type*} (b : ℕ → α) (s k : ℕ) : Fin k → α := fun l => b (s + l)

/-- A tuple extended by zero to a sequence. -/
private def extendZero {α : Type*} [Zero α] {n : ℕ} (a : Fin n → α) : ℕ → α :=
  fun i => if h : i < n then a ⟨i, h⟩ else 0

private theorem seg_extendZero {α : Type*} [Zero α] {n : ℕ} (a : Fin n → α) :
    seg (extendZero a) 0 n = a := by
  funext l
  simp [seg, extendZero]

/-- The composite `F ⋆ G` of two families of components. -/
private def famComp {α : Type*} (F : (n : ℕ) → (Fin n → α) → (M' →ₗ[R] M''))
    (G : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M')) : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M'') :=
  fun n a => ∑ k : Fin (n + 1), F (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩) ∘ₗ
    G k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩)

private theorem famComp_seg {α : Type*} (F : (n : ℕ) → (Fin n → α) → (M' →ₗ[R] M''))
    (G : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M')) (b : ℕ → α) (t p : ℕ) :
    famComp F G p (seg b t p) =
      ∑ k ∈ range (p + 1), F (p - k) (seg b (t + k) (p - k)) ∘ₗ G k (seg b t k) := by
  rw [famComp, ← Fin.sum_univ_eq_sum_range
    (fun k => F (p - k) (seg b (t + k) (p - k)) ∘ₗ G k (seg b t k))]
  refine sum_congr rfl fun k _ => ?_
  congr 2
  funext l
  simp [seg, add_assoc]

private theorem famComp_assoc {α : Type*} [Zero α] (F : (n : ℕ) → (Fin n → α) → (M'' →ₗ[R] N))
    (G : (n : ℕ) → (Fin n → α) → (M' →ₗ[R] M'')) (H : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M')) :
    famComp (famComp F G) H = famComp F (famComp G H) := by
  funext n a
  rw [← seg_extendZero a]
  generalize extendZero a = b
  ext m
  simp only [famComp_seg, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, zero_add]
  -- Both sides sum over `k ≤ i ≤ n`, the left one with `i = k + j`.
  let T (k j : ℕ) :=
    F (n - (k + j)) (seg b (k + j) (n - (k + j))) (G j (seg b k j) (H k (seg b 0 k) m))
  calc _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1 - k), T k j :=
        sum_congr rfl fun k hk => by
          rw [show n - k + 1 = n + 1 - k by simp at hk; omega]
          exact sum_congr rfl fun j _ => by rw [Nat.sub_sub]
    _ = ∑ i ∈ range (n + 1), ∑ k ∈ range (i + 1), T k (i - k) := (sum_range_diag_flip _ _).symm
    _ = _ := sum_congr rfl fun i _ => sum_congr rfl fun k hk => by
          simp only [T]
          rw [Nat.add_sub_cancel' (by simpa [Nat.lt_succ_iff] using hk)]

private theorem famComp_add_left {α : Type*} (F F' : (n : ℕ) → (Fin n → α) → (M' →ₗ[R] M''))
    (G : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M')) :
    famComp (F + F') G = famComp F G + famComp F' G := by
  funext n a
  simp [famComp, LinearMap.add_comp, sum_add_distrib]

private theorem famComp_add_right {α : Type*} (F : (n : ℕ) → (Fin n → α) → (M' →ₗ[R] M''))
    (G G' : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M')) :
    famComp F (G + G') = famComp F G + famComp F G' := by
  funext n a
  simp [famComp, LinearMap.comp_add, sum_add_distrib]

private theorem update_seg {α : Type*} (b : ℕ → α) (t p : ℕ) (i : Fin p) (x : α) :
    Function.update (seg b t p) i x = seg (Function.update b (t + i) x) t p := by
  funext l
  simp only [seg, Function.update_apply, Fin.ext_iff, Nat.add_left_cancel_iff]

private theorem seg_update_of_lt {α : Type*} (b : ℕ → α) {s k j : ℕ} (h : j < s ∨ s + k ≤ j)
    (x : α) : seg (Function.update b j x) s k = seg b s k := by
  funext l
  simp only [seg]
  rw [Function.update_of_ne (by omega)]

private theorem seg_update_lt {α : Type*} (b : ℕ → α) {i k : ℕ} (hk : i < k) (x : α) :
    seg (Function.update b i x) 0 k = Function.update (seg b 0 k) ⟨i, hk⟩ x := by
  rw [update_seg, zero_add]

private theorem seg_update_ge {α : Type*} (b : ℕ → α) {n i k : ℕ} (hk : k ≤ i) (hi : i < n)
    (x : α) : seg (Function.update b i x) k (n - k) =
      Function.update (seg b k (n - k)) ⟨i - k, by omega⟩ x := by
  rw [update_seg, Nat.add_sub_cancel' hk]

/-- The differential terms `∑_l F_{n+1}(m, a₁, …, d aₗ, …, aₙ)` of a family. -/
private def famDiff (F : (n : ℕ) → (Fin n → A) → (M →ₗ[R] N)) :
    (n : ℕ) → (Fin n → A) → (M →ₗ[R] N) :=
  fun n a => ∑ l : Fin n, F n (Function.update a l (d (a l)))

private theorem famDiff_seg (F : (n : ℕ) → (Fin n → A) → (M →ₗ[R] N)) (b : ℕ → A) (t p : ℕ) :
    famDiff (d := d) F p (seg b t p) =
      ∑ l ∈ range p, F p (seg (Function.update b (t + l) (d (b (t + l)))) t p) := by
  rw [famDiff, ← Fin.sum_univ_eq_sum_range
    (fun l => F p (seg (Function.update b (t + l) (d (b (t + l)))) t p))]
  exact sum_congr rfl fun l _ => by rw [update_seg]; rfl

/-- The differential terms are a derivation for the composite of families. -/
private theorem famDiff_famComp (F : (n : ℕ) → (Fin n → A) → (M' →ₗ[R] M''))
    (G : (n : ℕ) → (Fin n → A) → (M →ₗ[R] M')) :
    famDiff (d := d) (famComp F G) =
      famComp (famDiff (d := d) F) G + famComp F (famDiff (d := d) G) := by
  funext n a
  rw [← seg_extendZero a]
  generalize extendZero a = b
  ext m
  simp only [famDiff_seg, famComp_seg, Pi.add_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_sum, zero_add]
  -- In the term `(k, l)`, the input `d aₗ` goes to `G` when `l < k` and to `F` when `k ≤ l`.
  rw [sum_comm, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [← sum_range_add_sum_Ico _ (show k ≤ n by omega), sum_Ico_eq_sum_range, add_comm]
  congr 1
  · refine sum_congr rfl fun l _ => ?_
    rw [seg_update_of_lt b (s := 0) (k := k) (Or.inr (by omega))]
  · refine sum_congr rfl fun l hl => ?_
    rw [mem_range] at hl
    rw [seg_update_of_lt b (s := k) (Or.inl hl)]

/-- The product terms `∑_l F_n(m, a₁, …, aₗ aₗ₊₁, …, aₙ)` of a family. -/
private def famMul {α : Type*} [Mul α] (F : (n : ℕ) → (Fin n → α) → (M →ₗ[R] N)) :
    (n : ℕ) → (Fin n → α) → (M →ₗ[R] N)
  | 0, _ => 0
  | n + 1, a => ∑ l : Fin n, F n (Fin.contractNth l.castSucc (· * ·) a)

private theorem famMul_zero {α : Type*} [Mul α] (F : (n : ℕ) → (Fin n → α) → (M →ₗ[R] N))
    (a : Fin 0 → α) :
    famMul F 0 a = 0 :=
  (rfl)

/-- The sequence `b` with the product `b j * b (j + 1)` in place of the two entries `b j` and
`b (j + 1)`. -/
private def contractAt {α : Type*} [Mul α] (b : ℕ → α) (j : ℕ) : ℕ → α :=
  fun i => if i < j then b i else if i = j then b i * b (i + 1) else b (i + 1)

private theorem contractNth_seg {α : Type*} [Mul α] (b : ℕ → α) (t p : ℕ) (l : Fin p) :
    Fin.contractNth l.castSucc (· * ·) (seg b t (p + 1)) = seg (contractAt b (t + l)) t p := by
  funext i
  simp only [Fin.contractNth, seg, contractAt, Fin.val_castSucc, Fin.val_succ]
  by_cases h₁ : (i : ℕ) < l
  · simp [h₁]
  · by_cases h₂ : (i : ℕ) = l
    · simp [h₂, add_assoc]
    · simp [h₁, h₂, add_assoc]

private theorem seg_contractAt_of_le {α : Type*} [Mul α] (b : ℕ → α) {s k j : ℕ} (h : s + k ≤ j) :
    seg (contractAt b j) s k = seg b s k := by
  funext l
  simp only [seg, contractAt]
  rw [ite_eq_left (by omega)]

private theorem seg_contractAt_of_lt {α : Type*} [Mul α] (b : ℕ → α) {s k j : ℕ} (h : j < s) :
    seg (contractAt b j) s k = seg b (s + 1) k := by
  funext l
  simp only [seg, contractAt]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), add_right_comm]

private theorem famMul_seg {α : Type*} [Mul α] (F : (n : ℕ) → (Fin n → α) → (M →ₗ[R] N))
    (b : ℕ → α) (t p : ℕ) :
    famMul F (p + 1) (seg b t (p + 1)) =
      ∑ l ∈ range p, F p (seg (contractAt b (t + l)) t p) := by
  rw [famMul, ← Fin.sum_univ_eq_sum_range (fun l => F p (seg (contractAt b (t + l)) t p))]
  exact sum_congr rfl fun l _ => by rw [contractNth_seg]

/-- The product terms are a derivation for the composite of families. -/
private theorem famMul_famComp {α : Type*} [Zero α] [Mul α]
    (F : (n : ℕ) → (Fin n → α) → (M' →ₗ[R] M'')) (G : (n : ℕ) → (Fin n → α) → (M →ₗ[R] M')) :
    famMul (famComp F G) = famComp (famMul F) G + famComp F (famMul G) := by
  funext n a
  rw [← seg_extendZero a]
  generalize extendZero a = b
  ext m
  cases n with
  | zero => simp [famComp_seg, famMul_zero]
  | succ p =>
    simp only [famMul_seg, famComp_seg, Pi.add_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, zero_add]
    -- The last term of the first sum and the first term of the second vanish.
    have h₁ : ∑ k ∈ range (p + 1 + 1), famMul F (p + 1 - k) (seg b k (p + 1 - k))
        (G k (seg b 0 k) m) = ∑ k ∈ range (p + 1), famMul F (p - k + 1) (seg b k (p - k + 1))
          (G k (seg b 0 k) m) := by
      rw [sum_range_succ, Nat.sub_self, famMul_zero, LinearMap.zero_apply, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [show p + 1 - k = p - k + 1 by simp at hk; omega]
    have h₂ : ∑ k ∈ range (p + 1 + 1), F (p + 1 - k) (seg b k (p + 1 - k))
        (famMul G k (seg b 0 k) m) = ∑ k ∈ range (p + 1), F (p - k) (seg b (k + 1) (p - k))
          (famMul G (k + 1) (seg b 0 (k + 1)) m) := by
      rw [sum_range_succ', famMul_zero, LinearMap.zero_apply, map_zero, add_zero]
      refine sum_congr rfl fun k _ => ?_
      rw [show p + 1 - (k + 1) = p - k by omega]
    -- In the term `(k, l)`, the product `aₗ aₗ₊₁` goes to `G` when `l < k` and to `F` when
    -- `k ≤ l`.
    rw [h₁, h₂, sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [famMul_seg, famMul_seg, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
      ← sum_range_add_sum_Ico _ (show k ≤ p by omega), sum_Ico_eq_sum_range, add_comm]
    congr 1
    · refine sum_congr rfl fun l _ => ?_
      rw [seg_contractAt_of_le b (s := 0) (k := k) (by omega)]
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_range] at hl
      rw [seg_contractAt_of_lt b (s := k) hl, zero_add]

/-- The relation of a morphism, as an equation of families. -/
private theorem relation_eq_famComp
    (Φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'))
    (n : ℕ) (a : Fin n → A) (m : M) :
    ∑ k : Fin (n + 1), Φ (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (Mm.act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ∑ k : Fin (n + 1), Mm'.act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (Φ k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ungradedStasheffDiff Φ d n a m + ungradedStasheffMul Φ n a m =
    (famComp (fun n a => Φ n a) (fun n a => Mm.act n a) +
      famComp (fun n a => Mm'.act n a) (fun n a => Φ n a) + famDiff (d := d) (fun n a => Φ n a) +
      famMul (fun n a => Φ n a)) n a m := by
  have hmul : ungradedStasheffMul Φ n a m = famMul (fun n a => Φ n a) n a m := by
    cases n <;> simp [famMul, ungradedStasheffMul_succ, LinearMap.sum_apply]
  simp [famComp, famDiff, ungradedStasheffDiff_def, LinearMap.sum_apply, hmul]

private theorem famRelation (f : UngradedAInfinityRightModuleHom Mm Mm') :
    famComp (fun n a => f.map n a) (fun n a => Mm.act n a) +
      famComp (fun n a => Mm'.act n a) (fun n a => f.map n a) +
        famDiff (d := d) (fun n a => f.map n a) + famMul (fun n a => f.map n a) = 0 := by
  funext n a
  ext m
  rw [← relation_eq_famComp, f.stasheff]
  rfl

/-- The relations of `f` and `g` give that of `g ⋆ f`, in characteristic two. -/
private theorem famRelation_famComp [CharP R 2] {μ : (n : ℕ) → (Fin n → A) → (M →ₗ[R] M)}
    {μ' : (n : ℕ) → (Fin n → A) → (M' →ₗ[R] M')} {μ'' : (n : ℕ) → (Fin n → A) → (M'' →ₗ[R] M'')}
    {f : (n : ℕ) → (Fin n → A) → (M →ₗ[R] M')} {g : (n : ℕ) → (Fin n → A) → (M' →ₗ[R] M'')}
    (hf : famComp f μ + famComp μ' f + famDiff (d := d) f + famMul f = 0)
    (hg : famComp g μ' + famComp μ'' g + famDiff (d := d) g + famMul g = 0) :
    famComp (famComp g f) μ + famComp μ'' (famComp g f) + famDiff (d := d) (famComp g f) +
      famMul (famComp g f) = 0 := by
  have hf' : famComp f μ + famDiff (d := d) f + famMul f = famComp μ' f :=
    (add_eq_zero_iff_eq_of_charTwo R).mp (by rw [← hf]; abel)
  have hg' : famComp μ'' g + famDiff (d := d) g + famMul g = famComp g μ' :=
    (add_eq_zero_iff_eq_of_charTwo R).mp (by rw [← hg]; abel)
  have h : famComp (famComp g f) μ + famComp μ'' (famComp g f) + famDiff (d := d) (famComp g f) +
      famMul (famComp g f) = famComp g (famComp f μ + famDiff (d := d) f + famMul f) +
        famComp (famComp μ'' g + famDiff (d := d) g + famMul g) f := by
    rw [famComp_assoc, ← famComp_assoc μ'', famDiff_famComp, famMul_famComp]
    simp only [famComp_add_left, famComp_add_right]
    abel
  rw [h, hf', hg', famComp_assoc, add_self_eq_zero_of_charTwo R]

/-- The components of the composite morphism, as multilinear maps. -/
private def compMap (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'') where
  toFun := famComp (fun n a => g.map n a) (fun n a => f.map n a) n
  map_update_add' a i x y := by
    obtain rfl : ‹DecidableEq (Fin n)› = instDecidableEqFin n := Subsingleton.elim _ _
    rw [← seg_extendZero a]
    generalize extendZero a = b
    simp only [update_seg, zero_add, famComp_seg, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    -- The input `i` goes to `f` when `i < k` and to `g` when `k ≤ i`.
    by_cases hik : (i : ℕ) < k
    · have h₁ (z : A) := seg_update_of_lt b (s := k) (k := n - k) (Or.inl hik) z
      have h₂ (z : A) := seg_update_lt b hik z
      simp only [h₁, h₂, MultilinearMap.map_update_add, LinearMap.comp_add]
    · push Not at hik
      have h₁ (z : A) := seg_update_of_lt b (s := 0) (k := k) (j := i) (Or.inr (by omega)) z
      have h₂ (z : A) := seg_update_ge b hik i.isLt z
      simp only [h₁, h₂, MultilinearMap.map_update_add, LinearMap.add_comp]
  map_update_smul' a i c x := by
    obtain rfl : ‹DecidableEq (Fin n)› = instDecidableEqFin n := Subsingleton.elim _ _
    rw [← seg_extendZero a]
    generalize extendZero a = b
    simp only [update_seg, zero_add, famComp_seg, smul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    by_cases hik : (i : ℕ) < k
    · have h₁ (z : A) := seg_update_of_lt b (s := k) (k := n - k) (Or.inl hik) z
      have h₂ (z : A) := seg_update_lt b hik z
      simp only [h₁, h₂, MultilinearMap.map_update_smul, LinearMap.comp_smul]
    · push Not at hik
      have h₁ (z : A) := seg_update_of_lt b (s := 0) (k := k) (j := i) (Or.inr (by omega)) z
      have h₂ (z : A) := seg_update_ge b hik i.isLt z
      simp only [h₁, h₂, MultilinearMap.map_update_smul, LinearMap.smul_comp]

/-- The **composite** `g ∘ f` of morphisms of `A∞` modules, over a ring of characteristic two:
`(g ∘ f)_{n+1}(m, a₁, …, aₙ) = ∑_{i + j = n} g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
(`TauCeti.UngradedAInfinityRightModuleHom.comp_map_apply`). -/
noncomputable def comp [CharP R 2] (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') : UngradedAInfinityRightModuleHom Mm Mm'' where
  map := compMap g f
  stasheff n a m := by
    rw [relation_eq_famComp]
    exact LinearMap.congr_fun (congrFun (congrFun
      (famRelation_famComp f.famRelation g.famRelation) n) a) m

/-- The components of the composite: `(g ∘ f)_{n+1}(m, a…)` is the sum over `i + j = n` of
`g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`. -/
theorem comp_map_apply [CharP R 2] (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) (a : Fin n → A) (m : M) :
    (g.comp f).map n a m = ∑ k : Fin (n + 1), g.map (n - k)
      (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (f.map k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) := by
  simp [comp, compMap, famComp, LinearMap.sum_apply]

private theorem comp_map_seg [CharP R 2] (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (b : ℕ → A) (t n : ℕ) (m : M) :
    (g.comp f).map n (seg b t n) m = ∑ k ∈ range (n + 1),
      g.map (n - k) (seg b (t + k) (n - k)) (f.map k (seg b t k) m) := by
  simp only [comp, compMap, MultilinearMap.coe_mk, famComp_seg, LinearMap.sum_apply,
    LinearMap.comp_apply]

/-- The first component of the composite is the composite of the first components. -/
@[simp]
theorem comp_map_zero [CharP R 2] (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (a : Fin 0 → A) (m : M) :
    (g.comp f).map 0 a m = g.map 0 a (f.map 0 a m) := by
  rw [comp_map_apply, Fin.sum_univ_one]
  congr 2
  funext l
  exact absurd l.isLt (by simp)

/-- Composition of morphisms of `A∞` modules is associative. -/
theorem comp_assoc [CharP R 2] {Nn : UngradedAInfinityRightModule d N}
    (h : UngradedAInfinityRightModuleHom Mm'' Nn) (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') : (h.comp g).comp f = h.comp (g.comp f) := by
  ext n a m
  exact LinearMap.congr_fun (congrFun (congrFun (famComp_assoc (fun n a => h.map n a)
    (fun n a => g.map n a) (fun n a => f.map n a)) n) a) m

@[simp]
theorem id_comp [CharP R 2] (f : UngradedAInfinityRightModuleHom Mm Mm') : (id Mm').comp f = f := by
  ext n a m
  rw [← seg_extendZero a, comp_map_seg, sum_eq_single n (fun k hk hkn => by
    rw [mem_range] at hk
    obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_lt (show k < n by omega)
    rw [show n - k = p + 1 by omega, id_map_add_one, zero_apply, LinearMap.zero_apply]) (by simp),
    Nat.sub_self]
  exact id_map_zero _ _

@[simp]
theorem comp_id [CharP R 2] (f : UngradedAInfinityRightModuleHom Mm Mm') : f.comp (id Mm) = f := by
  ext n a m
  rw [← seg_extendZero a, comp_map_seg, sum_eq_single 0 (fun k _ hk0 => by
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [id_map_add_one, zero_apply, LinearMap.zero_apply, map_zero]) (by simp),
    Nat.sub_zero, id_map_zero, zero_add]

end Composition

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
