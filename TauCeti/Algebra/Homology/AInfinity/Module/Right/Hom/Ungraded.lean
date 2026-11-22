/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.LinearAlgebra.Multilinear.CompSplit

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
tensor products (`TauCeti.LowDimTopology.Bordered.TypeA.Basic`). Tau Ceti's morphisms of graded `A∞`
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
* **Sums and homotopies.** The relations are linear in the components, so morphisms add
  componentwise. A homotopy between morphisms `f` and `g`
  (`TauCeti.UngradedAInfinityRightModuleHom.Homotopy`) is a family `h_{n+1}` whose relation of
  every length sums to `f_{n+1} + g_{n+1}` instead of `0`. Over a ring of characteristic two it
  gives a morphism `(id, h)` from `M` into the mapping cone of `f + g`
  (`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`); through this morphism homotopic
  morphisms induce homotopic maps of box tensor products
  (`TauCeti.LowDimTopology.Bordered.TypeA.Homotopy`).
* **Composition.** Over a ring of characteristic two, morphisms `f : M → M'` and `g : M' → M''`
  compose (`TauCeti.UngradedAInfinityRightModuleHom.comp`), with components
  `(g ∘ f)_{n+1}(m, a₁, …, aₙ) = ∑_{i + j = n} g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`.
  The relation of length `n` of the composite is the sum of the relations of `f` of length `s`
  followed by `g`, and of the relations of `g` of length `n - s` applied to the output of `f`, for
  `s ≤ n`: the terms with an operation of `M'` between `f` and `g` occur in both families and
  cancel. Composition is associative, with the identity morphisms as units.
* **Strict units.** A morphism is strictly unital for a family `ι` of elements of the algebra
  (`TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital`) when its components `f_{n+1}`,
  `n ≥ 1`, vanish on every input tuple containing some `ι s`, and likewise for homotopies
  (`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.IsStrictlyUnital`). Strict morphisms, sums
  and composites of strictly unital morphisms are strictly unital, the mapping cone of a strictly
  unital morphism of strictly unital modules is a strictly unital module, and a strictly unital
  homotopy gives a strictly unital morphism into a mapping cone. For strictly unital modules
  whose idempotents are cycles, the maps induced by strictly unital morphisms and homotopies
  preserve the box tensor products over the idempotents
  (`TauCeti.LowDimTopology.Bordered.TypeA.Invariance`).

## Main definitions

* `TauCeti.UngradedAInfinityRightModuleHom`: a morphism of ungraded `A∞` right modules.
* `TauCeti.UngradedAInfinityRightModuleHom.cone`: its mapping cone.
* `TauCeti.UngradedAInfinityRightModuleHom.ofLinearMap`: the strict morphism of a linear map
  commuting with the operations.
* `TauCeti.UngradedAInfinityRightModuleHom.id`: the identity morphism.
* `TauCeti.UngradedAInfinityRightModuleHom.Homotopy`: a homotopy between two morphisms.
* `TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`: a homotopy between `f` and `g` as
  a morphism into the mapping cone of `f + g`.
* `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModuleHom`: an `A`-linear chain map of
  differential modules as a morphism of `A∞` modules.
* `TauCeti.UngradedAInfinityRightModuleHom.comp`: the composite of two morphisms.
* `TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital` and
  `TauCeti.UngradedAInfinityRightModuleHom.Homotopy.IsStrictlyUnital`: strictly unital morphisms
  and homotopies.

## Main results

* `TauCeti.UngradedAInfinityRightModuleHom.comp_map_apply`: the components of a composite.
* `TauCeti.UngradedAInfinityRightModuleHom.comp_id`,
  `TauCeti.UngradedAInfinityRightModuleHom.id_comp` and
  `TauCeti.UngradedAInfinityRightModuleHom.comp_assoc`: the identity and associativity laws.
* `TauCeti.UngradedAInfinityRightModuleHom.add_comp` and
  `TauCeti.UngradedAInfinityRightModuleHom.comp_add`: composition is additive in each argument.
* `TauCeti.UngradedAInfinityRightModuleHom.ofLinearMap_comp_ofLinearMap`: the composite of strict
  morphisms is strict.
* `TauCeti.UngradedAInfinityRightModuleHom.comp_map_eq_zero`: the components of a composite of
  morphisms with bounded components are bounded.
* `TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital.comp` and
  `TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital.cone`: composites of strictly unital
  morphisms are strictly unital, and so are the mapping cones of strictly unital morphisms of
  strictly unital modules.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.1 (morphisms of `A∞` modules over `𝔽₂`, their homotopies and strict unitality).
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
    simp [ungradedStasheffDiff_apply, coneAct_apply, Prod.fst_sum, Prod.snd_sum, sum_add_distrib]

private theorem stasheffMul_coneAct (n : ℕ) (a : Fin n → A) (p : M × M') :
    ungradedStasheffMul f.coneAct n a p =
      (ungradedStasheffMul Mm.act n a p.1,
        ungradedStasheffMul Mm'.act n a p.2 + ungradedStasheffMul f.map n a p.1) := by
  cases n with
  | zero => simp [Prod.zero_eq_mk]
  | succ n =>
    refine Prod.ext ?_ ?_ <;>
      simp [ungradedStasheffMul_succ_apply, coneAct_apply, Prod.fst_sum, Prod.snd_sum,
        sum_add_distrib]

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

/-- Composing a family of maps after a strict morphism, in the composite terms of a relation,
leaves only the map of full arity applied after `L`. -/
private theorem sum_strictMap {N : Type*} [AddCommGroup N] [Module R N] (L : M →ₗ[R] M')
    (φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] N)) (n : ℕ)
    (a : Fin n → A) (m : M) :
    ∑ k : Fin (n + 1), φ (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
      (strictMap L k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) =
        φ n a (L m) := by
  rw [sum_eq_single 0 (fun k _ hk => by
    rw [strictMap_eq_zero L (Fin.val_ne_zero_iff.mpr hk), zero_apply,
      LinearMap.zero_apply, map_zero]) (by simp)]
  rw [strictMap_apply_of_eq_zero L (Fin.val_zero (n + 1))]
  simp only [Fin.val_zero, zero_add, Fin.eta]
  -- The arity `n - 0` is `n` by definition.
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
    have h₂ := sum_strictMap L Mm'.act n a m
    have hdiff : ungradedStasheffDiff (strictMap L) d n a m = 0 := by
      cases n with
      | zero => simp [ungradedStasheffDiff_apply]
      | succ n => simp [ungradedStasheffDiff_apply, strictMap_eq_zero]
    have hmul : ungradedStasheffMul (strictMap L) n a m = 0 := by
      rcases n with _ | _ | n
      · simp
      · simp [ungradedStasheffMul_succ_apply]
      · simp [ungradedStasheffMul_succ_apply, strictMap_eq_zero]
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

/-- The components of the identity morphism are those of the strict morphism with `f₁ = id`, by
the definition of `id` as `ofLinearMap Mm Mm LinearMap.id`. -/
private theorem id_map_eq_strictMap [CharP R 2] : (id Mm).map = strictMap LinearMap.id :=
  (rfl)

/-- The components of the identity morphism vanish in every positive arity. -/
theorem id_map_eq_zero [CharP R 2] {n : ℕ} (hn : n ≠ 0) : (id Mm).map n = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact id_map_add_one n

/-! ### Sums of morphisms -/

/-- The **sum** of two morphisms, componentwise: `(f + g)_{n+1} = f_{n+1} + g_{n+1}`. Every term
of the relations is additive in the components, so the relations of `f + g` are the sums of
those of `f` and `g`. -/
instance : Add (UngradedAInfinityRightModuleHom Mm Mm') where
  add f g :=
    { map := fun n => f.map n + g.map n
      stasheff := fun n a m => by
        convert congrArg₂ (· + ·) (f.stasheff n a m) (g.stasheff n a m) using 1
        · rw [ungradedStasheffDiff_add, ungradedStasheffMul_add]
          simp only [add_apply, LinearMap.add_apply, map_add, sum_add_distrib]
          abel
        · rw [add_zero] }

@[simp]
theorem add_map (f g : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) :
    (f + g).map n = f.map n + g.map n :=
  (rfl)

/-! ### Homotopies -/

/-- A **homotopy** between morphisms `f` and `g` of ungraded `A∞` right modules from `M` to `M'`: a
family of maps `h_{n+1} : M ⊗ A^{⊗ n} → M'`, here `map n`, whose morphism relation of every length
`n` sums to `f_{n+1} + g_{n+1}` instead of `0`:

`∑_{i + j = n} h_{j+1}(m_{i+1}(m, a₁, …, aᵢ), …) + ∑_{i + j = n} m'_{j+1}(h_{i+1}(m, a₁, …, aᵢ), …)`
`  + ∑_l h_{n+1}(m, …, d aₗ, …) + ∑_l h_n(m, …, aₗ aₗ₊₁, …) = f_{n+1}(m, a…) + g_{n+1}(m, a…)`.

Over a ring of characteristic two this is the relation `f - g = ∂h` of a homotopy of `A∞`
morphisms, every sign being `1`. Its length-zero case says that `h₁` is a chain homotopy between
`f₁` and `g₁`. -/
@[ext]
structure Homotopy (f g : UngradedAInfinityRightModuleHom Mm Mm') where
  /-- The component `h_{n+1}`, with `n` algebra inputs. -/
  map : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')
  /-- The homotopy relation of length `n`. -/
  stasheff (n : ℕ) (a : Fin n → A) (m : M) :
    ∑ k : Fin (n + 1), map (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (Mm.act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ∑ k : Fin (n + 1), Mm'.act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (map k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ungradedStasheffDiff map d n a m + ungradedStasheffMul map n a m =
    f.map n a m + g.map n a m

namespace Homotopy

variable [CharP R 2] {f g : UngradedAInfinityRightModuleHom Mm Mm'} (H : Homotopy f g)

/-- The components `(id_{n+1}, h_{n+1})` of the morphism
`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`. -/
private noncomputable def coneHomMap (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M × M') where
  toFun a := ((id Mm).map n a).prod (H.map n a)
  map_update_add' a i x y := by
    ext <;> simp [MultilinearMap.map_update_add]
  map_update_smul' a i c x := by
    ext <;> simp [MultilinearMap.map_update_smul]

private theorem coneHomMap_apply (n : ℕ) (a : Fin n → A) (m : M) :
    H.coneHomMap n a m = ((id Mm).map n a m, H.map n a m) :=
  (rfl)

private theorem stasheffDiff_coneHomMap (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffDiff H.coneHomMap d n a m =
      (ungradedStasheffDiff (id Mm).map d n a m, ungradedStasheffDiff H.map d n a m) := by
  refine Prod.ext ?_ ?_ <;>
    simp [ungradedStasheffDiff_apply, coneHomMap_apply, Prod.fst_sum, Prod.snd_sum]

private theorem stasheffMul_coneHomMap (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffMul H.coneHomMap n a m =
      (ungradedStasheffMul (id Mm).map n a m, ungradedStasheffMul H.map n a m) := by
  cases n with
  | zero => simp [Prod.zero_eq_mk]
  | succ n =>
    refine Prod.ext ?_ ?_ <;>
      simp [ungradedStasheffMul_succ_apply, coneHomMap_apply, Prod.fst_sum, Prod.snd_sum]

/-- **A homotopy as a morphism into a mapping cone.** Over a ring of characteristic two, a
homotopy `h` between `f` and `g` gives the morphism `(id, h)` from `M` to the mapping cone of
`f + g`, with components `(id_{n+1}, h_{n+1})`. The first component of its relation is that of
the identity, and the second is the homotopy relation, where the cone contributes
`(f + g)_{n+1}(m, a…)`, which cancels `f_{n+1} + g_{n+1}`. -/
noncomputable def toConeHom : UngradedAInfinityRightModuleHom Mm (f + g).cone where
  map := H.coneHomMap
  stasheff n a m := by
    rw [stasheffDiff_coneHomMap, stasheffMul_coneHomMap]
    refine Prod.ext ?_ ?_
    · simpa [coneHomMap_apply, Prod.fst_sum] using (id Mm).stasheff n a m
    · simp only [coneHomMap_apply, cone_act_apply, Prod.snd_add, Prod.snd_sum, Prod.snd_zero,
        sum_add_distrib]
      rw [id_map_eq_strictMap, sum_strictMap]
      simp only [add_map, add_apply, LinearMap.add_apply, LinearMap.id_apply]
      have h := congrArg (· + (f.map n a m + g.map n a m)) (H.stasheff n a m)
      simp only [add_self_eq_zero_of_charTwo R] at h
      refine Eq.trans ?_ h
      abel

@[simp]
theorem toConeHom_map_apply (n : ℕ) (a : Fin n → A) (m : M) :
    H.toConeHom.map n a m = ((id Mm).map n a m, H.map n a m) :=
  (rfl)

end Homotopy

end UngradedAInfinityRightModuleHom

namespace UngradedAInfinityRightModuleHom

/-! ### Composition -/

section Comp

/-! The relations of a composite are checked on inputs written as segments `bᵢ, …, bᵢ₊ⱼ₋₁` of one
sequence `b : ℕ → A`. Splitting the inputs then only moves the endpoints of segments, and the
arities of the operations become natural numbers on which no tuple depends. -/

/-- The inputs `bᵢ, …, bᵢ₊ⱼ₋₁` of a sequence, as a tuple of length `j`. -/
private def seg (b : ℕ → A) (i j : ℕ) : Fin j → A := fun l => b (i + l)

/-- Every tuple is a segment of a sequence. -/
private theorem exists_eq_seg {n : ℕ} (a : Fin n → A) : ∃ b : ℕ → A, a = seg b 0 n :=
  ⟨fun t => if h : t < n then a ⟨t, h⟩ else 0, funext fun l => by simp [seg]⟩

/-- The sequence `b` with the consecutive inputs `bₚ` and `bₚ₊₁` replaced by their product. -/
private def contract (b : ℕ → A) (p : ℕ) : ℕ → A := fun t =>
  if t < p then b t else if t = p then b p * b (p + 1) else b (t + 1)

omit [Ring A] in
private theorem seg_update_of_lt {b : ℕ → A} {p i : ℕ} (j : ℕ) (x : A) (hp : p < i) :
    seg (Function.update b p x) i j = seg b i j :=
  funext fun _ => Function.update_of_ne (by omega) _ _

omit [Ring A] in
private theorem seg_update_of_le {b : ℕ → A} {p i j : ℕ} (x : A) (hp : i + j ≤ p) :
    seg (Function.update b p x) i j = seg b i j :=
  funext fun l => Function.update_of_ne (by have := l.isLt; omega) _ _

private theorem seg_contract_of_lt {b : ℕ → A} {p i : ℕ} (j : ℕ) (hp : p < i) :
    seg (contract b p) i j = seg b (i + 1) j :=
  funext fun l => by
    simp only [seg, contract, show ¬ i + (l : ℕ) < p by omega, show i + (l : ℕ) ≠ p by omega,
      ite_false, Nat.add_right_comm]

private theorem seg_contract_of_le {b : ℕ → A} {p i j : ℕ} (hp : i + j ≤ p) :
    seg (contract b p) i j = seg b i j :=
  funext fun l => by simp [seg, contract, show i + (l : ℕ) < p by have := l.isLt; omega]

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The operation `φ j` of a family on the segment of length `j` of `b` starting at `bᵢ`. -/
private def segOp (φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] N))
    (b : ℕ → A) (i j : ℕ) : M →ₗ[R] N :=
  φ j (seg b i j)

/-- The differential terms of a relation on a segment. -/
private theorem stasheffDiff_seg
    (φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] N))
    (b : ℕ → A) (i s : ℕ) (m : M) :
    ungradedStasheffDiff φ d s (seg b i s) m =
      ∑ l ∈ range s, segOp φ (Function.update b (i + l) (d (b (i + l)))) i s m := by
  rw [ungradedStasheffDiff_apply, ← Fin.sum_univ_eq_sum_range
    (fun l => segOp φ (Function.update b (i + l) (d (b (i + l)))) i s m)]
  refine sum_congr rfl fun l _ => ?_
  congr 2
  funext t
  by_cases ht : t = l
  · subst ht
    simp [seg]
  · have ht' : (t : ℕ) ≠ l := fun h => ht (Fin.ext h)
    simp only [seg, Function.update_of_ne ht]
    exact (Function.update_of_ne (by omega) _ _).symm

/-- The product terms of a relation on a segment. -/
private theorem stasheffMul_seg
    (φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] N))
    (b : ℕ → A) (i s : ℕ) (m : M) :
    ungradedStasheffMul φ s (seg b i s) m =
      ∑ l ∈ range (s - 1), segOp φ (contract b (i + l)) i (s - 1) m := by
  cases s with
  | zero => simp
  | succ s =>
    rw [ungradedStasheffMul_succ_apply, Nat.add_sub_cancel, ← Fin.sum_univ_eq_sum_range
      (fun l => segOp φ (contract b (i + l)) i s m)]
    refine sum_congr rfl fun l _ => ?_
    congr 2
    funext t
    rcases lt_trichotomy (t : ℕ) l with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
      simp [seg, contract, h]
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h)]
      simp [seg, contract, h, add_assoc]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]
      simp [seg, contract, show ¬ i + (t : ℕ) < i + l by omega, h.ne', add_assoc]

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- The composite terms of a relation on a segment. -/
private theorem sum_comp_seg
    (ψ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (N →ₗ[R] P))
    (φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] N))
    (b : ℕ → A) (i s : ℕ) (m : M) :
    ∑ k : Fin (s + 1), ψ (s - k) (fun l => seg b i s ⟨k + l, by have := l.isLt; omega⟩)
        (φ k (fun l => seg b i s ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) =
      ∑ k ∈ range (s + 1), segOp ψ b (i + k) (s - k) (segOp φ b i k m) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => segOp ψ b (i + k) (s - k) (segOp φ b i k m))]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun l : Fin (s - k) => seg b i s ⟨k + l, by have := l.isLt; omega⟩) =
      seg b (i + k) (s - k) := funext fun l => by simp [seg, add_assoc]
  have h' : (fun l : Fin k => seg b i s ⟨l, by have := l.isLt; have := k.isLt; omega⟩) =
      seg b i k := funext fun l => by simp [seg]
  rw [h, h', segOp, segOp]

variable {M'' : Type*} [AddCommGroup M''] [Module R M''] {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'} {Mm'' : UngradedAInfinityRightModule d M''}

/-- The components of a composite: `(g ∘ f)_{n+1}(m, a₁, …, aₙ)` is the sum over `i + j = n` of
`g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`. -/
private noncomputable def compMap (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'') :=
  ∑ k : Fin (n + 1), (g.map (n - k)).compSplit (f.map k) (by omega : (k : ℕ) + (n - k) = n)

private theorem compMap_apply (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) (a : Fin n → A) (m : M) :
    compMap g f n a m = ∑ k : Fin (n + 1), g.map (n - k)
      (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
      (f.map k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) := by
  simp only [compMap, _root_.sum_apply, LinearMap.sum_apply, MultilinearMap.compSplit_apply]

private theorem segOp_compMap (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') (b : ℕ → A) (i n : ℕ) (m : M) :
    segOp (compMap g f) b i n m =
      ∑ k ∈ range (n + 1), segOp g.map b (i + k) (n - k) (segOp f.map b i k m) := by
  rw [segOp, compMap_apply, sum_comp_seg]

/-- The relation of a morphism on a segment, with the arities and positions of all its terms. -/
private theorem stasheff_seg (f : UngradedAInfinityRightModuleHom Mm Mm') (b : ℕ → A)
    (i s : ℕ) (m : M) :
    ∑ k ∈ range (s + 1), segOp f.map b (i + k) (s - k) (segOp Mm.act b i k m) +
      ∑ k ∈ range (s + 1), segOp Mm'.act b (i + k) (s - k) (segOp f.map b i k m) +
      ∑ l ∈ range s, segOp f.map (Function.update b (i + l) (d (b (i + l)))) i s m +
      ∑ l ∈ range (s - 1), segOp f.map (contract b (i + l)) i (s - 1) m = 0 := by
  have h := f.stasheff s (seg b i s) m
  rwa [sum_comp_seg, sum_comp_seg, stasheffDiff_seg, stasheffMul_seg] at h

variable (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')

/-- The terms of the relation of a composite in which an operation of `M` is followed by the
composite are those of the relations of `f` followed by `g`. -/
private theorem sum_segOp_compMap_act (b : ℕ → A) (n : ℕ) (m : M) :
    ∑ k ∈ range (n + 1), segOp (compMap g f) b k (n - k) (segOp Mm.act b 0 k m) =
      ∑ s ∈ range (n + 1), segOp g.map b s (n - s)
        (∑ k ∈ range (s + 1), segOp f.map b k (s - k) (segOp Mm.act b 0 k m)) := by
  simp only [segOp_compMap, map_sum, Nat.sub_sub]
  rw [sum_range_succ_sum_range_succ_comm]
  simp only [Nat.add_sub_cancel_left]

/-- The terms of the relation of a composite in which the composite is followed by an operation
of `M''` are those of the relations of `g` following `f`. -/
private theorem sum_act_segOp_compMap (b : ℕ → A) (n : ℕ) (m : M) :
    ∑ k ∈ range (n + 1), segOp Mm''.act b k (n - k) (segOp (compMap g f) b 0 k m) =
      ∑ s ∈ range (n + 1), ∑ k ∈ range (n - s + 1), segOp Mm''.act b (s + k) (n - s - k)
        (segOp g.map b s k (segOp f.map b 0 s m)) := by
  simp only [segOp_compMap, zero_add, map_sum]
  rw [sum_range_succ_sum_range_succ_comm]
  simp only [Nat.add_sub_cancel_left, Nat.sub_sub]

/-- The terms with an operation of `M'` between `f` and `g`, which occur both in the relations of
`f` followed by `g` and in those of `g` following `f`. -/
private theorem sum_segOp_act_segOp (b : ℕ → A) (n : ℕ) (m : M) :
    ∑ s ∈ range (n + 1), segOp g.map b s (n - s)
        (∑ k ∈ range (s + 1), segOp Mm'.act b k (s - k) (segOp f.map b 0 k m)) =
      ∑ s ∈ range (n + 1), ∑ k ∈ range (n - s + 1), segOp g.map b (s + k) (n - s - k)
        (segOp Mm'.act b s k (segOp f.map b 0 s m)) := by
  simp only [map_sum]
  rw [sum_range_succ_sum_range_succ_comm]
  simp only [Nat.add_sub_cancel_left, Nat.sub_sub]

/-- The differential terms of a composite split into those of `f` and those of `g`. -/
private theorem sum_segOp_compMap_update (b : ℕ → A) (n : ℕ) (m : M) :
    ∑ l ∈ range n, segOp (compMap g f) (Function.update b l (d (b l))) 0 n m =
      ∑ s ∈ range (n + 1), segOp g.map b s (n - s)
          (∑ l ∈ range s, segOp f.map (Function.update b l (d (b l))) 0 s m) +
        ∑ s ∈ range (n + 1), ∑ l ∈ range (n - s),
          segOp g.map (Function.update b (s + l) (d (b (s + l)))) s (n - s)
            (segOp f.map b 0 s m) := by
  simp only [segOp_compMap, zero_add, map_sum]
  rw [sum_comm, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [← sum_range_add_sum_Ico _ (Nat.lt_succ_iff.mp (mem_range.mp hk)),
    sum_Ico_eq_sum_range]
  congr 1
  · refine sum_congr rfl fun l hl => ?_
    simp only [segOp, seg_update_of_lt (n - k) _ (mem_range.mp hl)]
  · refine sum_congr rfl fun l _ => ?_
    simp only [segOp, seg_update_of_le _ (by omega : 0 + k ≤ k + l)]

/-- The product terms of a composite split into those of `f` and those of `g`. -/
private theorem sum_segOp_compMap_contract (b : ℕ → A) (n : ℕ) (m : M) :
    ∑ l ∈ range (n - 1), segOp (compMap g f) (contract b l) 0 (n - 1) m =
      ∑ s ∈ range (n + 1), segOp g.map b s (n - s)
          (∑ l ∈ range (s - 1), segOp f.map (contract b l) 0 (s - 1) m) +
        ∑ s ∈ range (n + 1), ∑ l ∈ range (n - s - 1),
          segOp g.map (contract b (s + l)) s (n - s - 1) (segOp f.map b 0 s m) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ' _ (n + 1), sum_range_succ _ (n + 1)]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_sub, range_zero, sum_empty, map_zero,
      add_zero, Nat.add_sub_add_right, segOp_compMap, zero_add, map_sum,
      show ∀ k, n + 1 - k - 1 = n - k by omega]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [← sum_range_add_sum_Ico _ (Nat.lt_succ_iff.mp (mem_range.mp hk)),
      sum_Ico_eq_sum_range]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      simp only [segOp, seg_contract_of_lt (n - k) (mem_range.mp hl)]
    · refine sum_congr rfl fun l _ => ?_
      simp only [segOp, seg_contract_of_le (by omega : 0 + k ≤ k + l)]

/-- The relations of a composite: on segments, the relation of `g ∘ f` of length `n` is the sum of
the relations of `f` of length `s` followed by `g`, and of the relations of `g` of length `n - s`
following `f`, for `s ≤ n`. The terms with an operation of `M'` between `f` and `g` occur in both
and cancel in characteristic two. -/
private theorem compMap_stasheff [CharP R 2] (n : ℕ) (a : Fin n → A) (m : M) :
    ∑ k : Fin (n + 1), compMap g f (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (Mm.act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ∑ k : Fin (n + 1), Mm''.act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (compMap g f k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) +
      ungradedStasheffDiff (compMap g f) d n a m + ungradedStasheffMul (compMap g f) n a m = 0 := by
  obtain ⟨b, rfl⟩ := exists_eq_seg a
  rw [sum_comp_seg, sum_comp_seg, stasheffDiff_seg, stasheffMul_seg]
  simp only [zero_add]
  rw [sum_segOp_compMap_act, sum_act_segOp_compMap, sum_segOp_compMap_update,
    sum_segOp_compMap_contract]
  -- The relations of `f` of every length `s ≤ n`, followed by `g`.
  have hf : ∑ s ∈ range (n + 1), segOp g.map b s (n - s)
      (∑ k ∈ range (s + 1), segOp f.map b k (s - k) (segOp Mm.act b 0 k m) +
        ∑ k ∈ range (s + 1), segOp Mm'.act b k (s - k) (segOp f.map b 0 k m) +
        ∑ l ∈ range s, segOp f.map (Function.update b l (d (b l))) 0 s m +
        ∑ l ∈ range (s - 1), segOp f.map (contract b l) 0 (s - 1) m) = 0 :=
    sum_eq_zero fun s _ => by
      simpa only [zero_add, map_zero] using
        congrArg (segOp g.map b s (n - s)) (stasheff_seg f b 0 s m)
  -- The relations of `g` of every length `n - s`, following `f`.
  have hg : ∑ s ∈ range (n + 1),
      (∑ k ∈ range (n - s + 1), segOp g.map b (s + k) (n - s - k)
          (segOp Mm'.act b s k (segOp f.map b 0 s m)) +
        ∑ k ∈ range (n - s + 1), segOp Mm''.act b (s + k) (n - s - k)
          (segOp g.map b s k (segOp f.map b 0 s m)) +
        ∑ l ∈ range (n - s), segOp g.map (Function.update b (s + l) (d (b (s + l)))) s (n - s)
          (segOp f.map b 0 s m) +
        ∑ l ∈ range (n - s - 1), segOp g.map (contract b (s + l)) s (n - s - 1)
          (segOp f.map b 0 s m)) = 0 :=
    sum_eq_zero fun s _ => stasheff_seg g b s (n - s) (segOp f.map b 0 s m)
  simp only [map_add, sum_add_distrib] at hf hg
  rw [sum_segOp_act_segOp] at hf
  -- The terms common to both families of relations cancel.
  generalize ∑ s ∈ range (n + 1), ∑ k ∈ range (n - s + 1), segOp g.map b (s + k) (n - s - k)
    (segOp Mm'.act b s k (segOp f.map b 0 s m)) = c at hf hg
  linear_combination (norm := abel) hf + hg - add_self_eq_zero_of_charTwo R c

/-- The **composite** `g ∘ f` of morphisms of ungraded `A∞` right modules, over a ring of
characteristic two. Its components are
`(g ∘ f)_{n+1}(m, a₁, …, aₙ) = ∑_{i + j = n} g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
(`TauCeti.UngradedAInfinityRightModuleHom.comp_map_apply`). -/
noncomputable def comp [CharP R 2] (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') : UngradedAInfinityRightModuleHom Mm Mm'' where
  map := compMap g f
  stasheff := compMap_stasheff g f

/-- The components of a composite: `(g ∘ f)_{n+1}(m, a₁, …, aₙ)` is the sum over `i + j = n` of
`g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`. -/
theorem comp_map_apply [CharP R 2] (n : ℕ) (a : Fin n → A) (m : M) :
    (g.comp f).map n a m = ∑ k : Fin (n + 1), g.map (n - k)
      (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
      (f.map k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) :=
  compMap_apply g f n a m

/-- The first component of a composite is the composite of the first components. -/
@[simp]
theorem comp_map_zero [CharP R 2] (a : Fin 0 → A) (m : M) :
    (g.comp f).map 0 a m = g.map 0 a (f.map 0 a m) := by
  rw [comp_map_apply, Fin.sum_univ_one]
  congr 2
  funext l
  exact Fin.elim0 l

/-- If the components of `f` vanish from arity `K` on and those of `g` from arity `K'` on, the
components of the composite vanish from arity `K + K'` on. -/
theorem comp_map_eq_zero [CharP R 2] {K K' : ℕ} (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K' ≤ n → g.map n = 0) {n : ℕ} (hn : K + K' ≤ n) : (g.comp f).map n = 0 := by
  refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
  rw [comp_map_apply, _root_.zero_apply, LinearMap.zero_apply]
  refine sum_eq_zero fun k _ => ?_
  by_cases hk : K ≤ (k : ℕ)
  · rw [hf k hk, _root_.zero_apply, LinearMap.zero_apply, map_zero]
  · rw [hg (n - k) (by omega), _root_.zero_apply, LinearMap.zero_apply]

private theorem segOp_comp [CharP R 2] (b : ℕ → A) (i n : ℕ) (m : M) :
    segOp (g.comp f).map b i n m =
      ∑ k ∈ range (n + 1), segOp g.map b (i + k) (n - k) (segOp f.map b i k m) :=
  segOp_compMap g f b i n m

/-- The composite with the identity on the source is the morphism itself. -/
@[simp]
theorem comp_id [CharP R 2] : f.comp (id Mm) = f := by
  ext n a m
  obtain ⟨b, rfl⟩ := exists_eq_seg a
  refine (segOp_comp f (id Mm) b 0 n m).trans ?_
  rw [sum_range_succ', sum_eq_zero fun k _ => by simp [segOp], zero_add]
  simp [segOp]

/-- The composite with the identity on the target is the morphism itself. -/
@[simp]
theorem id_comp [CharP R 2] : (id Mm'').comp g = g := by
  ext n a m
  obtain ⟨b, rfl⟩ := exists_eq_seg a
  refine (segOp_comp (id Mm'') g b 0 n m).trans ?_
  rw [sum_range_succ, sum_eq_zero fun k hk => ?_, zero_add, Nat.sub_self]
  · simp [segOp]
  · obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by have := mem_range.mp hk; omega⟩
    rw [hj]
    simp [segOp]

/-- The composite of strict morphisms is the strict morphism of the composite linear map. -/
@[simp]
theorem ofLinearMap_comp_ofLinearMap [CharP R 2] (L : M →ₗ[R] M') (L' : M' →ₗ[R] M'')
    (hL : ∀ n a m, L (Mm.act n a m) = Mm'.act n a (L m))
    (hL' : ∀ n a m, L' (Mm'.act n a m) = Mm''.act n a (L' m)) :
    (ofLinearMap Mm' Mm'' L' hL').comp (ofLinearMap Mm Mm' L hL) =
      ofLinearMap Mm Mm'' (L' ∘ₗ L) fun n a m => by simp only [LinearMap.comp_apply, hL, hL'] := by
  ext n a m
  obtain ⟨b, rfl⟩ := exists_eq_seg a
  refine (segOp_comp _ _ b 0 n m).trans ?_
  rw [sum_range_succ', sum_eq_zero fun k _ => by simp [segOp], zero_add]
  cases n <;> simp [segOp]

/-- Composition of morphisms is associative. -/
@[simp]
theorem comp_assoc [CharP R 2] {Q : Type*} [AddCommGroup Q] [Module R Q]
    {Mq : UngradedAInfinityRightModule d Q} (h : UngradedAInfinityRightModuleHom Mm'' Mq) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext n a m
  obtain ⟨b, rfl⟩ := exists_eq_seg a
  refine (segOp_comp _ f b 0 n m).trans (Eq.trans ?_ (segOp_comp h _ b 0 n m).symm)
  simp only [segOp_comp, zero_add, map_sum, Nat.sub_sub]
  rw [sum_range_succ_sum_range_succ_comm]
  simp only [Nat.add_sub_cancel_left]

/-- Composition distributes over the sum of the morphisms composed after. -/
@[simp]
theorem add_comp [CharP R 2] (g₁ g₂ : UngradedAInfinityRightModuleHom Mm' Mm'') :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  ext n a m
  simp only [comp_map_apply, add_map, _root_.add_apply, LinearMap.add_apply, sum_add_distrib]

/-- Composition distributes over the sum of the morphisms composed first. -/
@[simp]
theorem comp_add [CharP R 2] (f₁ f₂ : UngradedAInfinityRightModuleHom Mm Mm') :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  ext n a m
  simp only [comp_map_apply, add_map, _root_.add_apply, LinearMap.add_apply, map_add,
    sum_add_distrib]

end Comp

/-! ### Strict units -/

section StrictUnit

variable {M'' : Type*} [AddCommGroup M''] [Module R M''] {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'} {Mm'' : UngradedAInfinityRightModule d M''}
  {S : Type*} {ι : S → A}

/-- A morphism of `A∞` modules is **strictly unital** for a family `ι` of elements of the algebra,
typically its idempotents, when every component `f_{n+1}`, `n ≥ 1`, vanishes as soon as one of its
algebra inputs is some `ι s`. The component `f₁` has no algebra input and is not constrained. -/
def IsStrictlyUnital (f : UngradedAInfinityRightModuleHom Mm Mm') (ι : S → A) : Prop :=
  ∀ n (a : Fin n → A) (i : Fin n) (s : S), a i = ι s → f.map n a = 0

/-- The defining property of a strictly unital morphism, for proving strict unitality without
unfolding the definition. -/
theorem isStrictlyUnital_iff {f : UngradedAInfinityRightModuleHom Mm Mm'} :
    f.IsStrictlyUnital ι ↔ ∀ n (a : Fin n → A) (i : Fin n) (s : S), a i = ι s → f.map n a = 0 :=
  Iff.rfl

/-- A component of a strictly unital morphism vanishes on a unit input. -/
theorem IsStrictlyUnital.map_eq_zero {f : UngradedAInfinityRightModuleHom Mm Mm'}
    (hf : f.IsStrictlyUnital ι) {n : ℕ} {a : Fin n → A} {i : Fin n} {s : S} (hi : a i = ι s) :
    f.map n a = 0 :=
  hf n a i s hi

/-- A morphism without higher components, `f_{n+1} = 0` for `n ≥ 1`, is strictly unital. -/
theorem isStrictlyUnital_of_map_add_one_eq_zero {f : UngradedAInfinityRightModuleHom Mm Mm'}
    (hf : ∀ n, f.map (n + 1) = 0) : f.IsStrictlyUnital ι := fun _ _ i _ _ => by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero i.pos.ne'
  rw [hf n, _root_.zero_apply]

/-- A strict morphism is strictly unital. -/
theorem isStrictlyUnital_ofLinearMap [CharP R 2] (L : M →ₗ[R] M')
    (hL : ∀ n a m, L (Mm.act n a m) = Mm'.act n a (L m)) :
    (ofLinearMap Mm Mm' L hL).IsStrictlyUnital ι :=
  isStrictlyUnital_of_map_add_one_eq_zero (ofLinearMap_map_add_one L hL)

/-- The identity morphism is strictly unital. -/
theorem isStrictlyUnital_id [CharP R 2] : (id Mm).IsStrictlyUnital ι :=
  isStrictlyUnital_of_map_add_one_eq_zero id_map_add_one

/-- A sum of strictly unital morphisms is strictly unital. -/
theorem IsStrictlyUnital.add {f g : UngradedAInfinityRightModuleHom Mm Mm'}
    (hf : f.IsStrictlyUnital ι) (hg : g.IsStrictlyUnital ι) : (f + g).IsStrictlyUnital ι :=
  fun _ _ _ _ hi => by
    rw [add_map, _root_.add_apply, hf.map_eq_zero hi, hg.map_eq_zero hi, add_zero]

/-- **A composite of strictly unital morphisms is strictly unital.** -/
theorem IsStrictlyUnital.comp [CharP R 2] {g : UngradedAInfinityRightModuleHom Mm' Mm''}
    {f : UngradedAInfinityRightModuleHom Mm Mm'} (hg : g.IsStrictlyUnital ι)
    (hf : f.IsStrictlyUnital ι) : (g.comp f).IsStrictlyUnital ι := by
  refine fun n a i s hi => LinearMap.ext fun m => ?_
  rw [comp_map_apply, LinearMap.zero_apply]
  -- In each term `g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`, the unit input lies among the
  -- inputs of `f_{i+1}` or among those of `g_{j+1}`.
  refine sum_eq_zero fun k _ => ?_
  by_cases hik : (i : ℕ) < k
  · rw [hf.map_eq_zero (i := ⟨i, hik⟩) (by simpa using hi), LinearMap.zero_apply, map_zero]
  · rw [hg.map_eq_zero (i := ⟨i - k, by omega⟩) (by rw [← hi]; congr 1; ext; simp; omega),
      LinearMap.zero_apply]

/-- **The mapping cone of a strictly unital morphism of strictly unital modules is strictly
unital.** -/
theorem IsStrictlyUnital.cone {f : UngradedAInfinityRightModuleHom Mm Mm'}
    (hf : f.IsStrictlyUnital ι) (hMm : Mm.IsStrictlyUnital ι) (hMm' : Mm'.IsStrictlyUnital ι) :
    f.cone.IsStrictlyUnital ι :=
  -- The operations of arity at least three of the cone are built from those of the two modules
  -- and the components of the morphism.
  (UngradedAInfinityRightModule.isStrictlyUnital_iff _).2 fun _ hn _ _ _ hi =>
    LinearMap.ext fun p => by
      simp [hMm.act_eq_zero hn hi, hMm'.act_eq_zero hn hi, hf.map_eq_zero hi]

/-- A homotopy between morphisms of `A∞` modules is **strictly unital** for a family `ι` of
elements of the algebra when every component `h_{n+1}`, `n ≥ 1`, vanishes as soon as one of its
algebra inputs is some `ι s`. -/
def Homotopy.IsStrictlyUnital {f g : UngradedAInfinityRightModuleHom Mm Mm'} (H : Homotopy f g)
    (ι : S → A) : Prop :=
  ∀ n (a : Fin n → A) (i : Fin n) (s : S), a i = ι s → H.map n a = 0

/-- The defining property of a strictly unital homotopy, for proving strict unitality without
unfolding the definition. -/
theorem Homotopy.isStrictlyUnital_iff {f g : UngradedAInfinityRightModuleHom Mm Mm'}
    {H : Homotopy f g} :
    H.IsStrictlyUnital ι ↔ ∀ n (a : Fin n → A) (i : Fin n) (s : S), a i = ι s → H.map n a = 0 :=
  Iff.rfl

/-- A component of a strictly unital homotopy vanishes on a unit input. -/
theorem Homotopy.IsStrictlyUnital.map_eq_zero {f g : UngradedAInfinityRightModuleHom Mm Mm'}
    {H : Homotopy f g} (hH : H.IsStrictlyUnital ι) {n : ℕ} {a : Fin n → A} {i : Fin n} {s : S}
    (hi : a i = ι s) : H.map n a = 0 :=
  hH n a i s hi

/-- **A strictly unital homotopy gives a strictly unital morphism into the mapping cone**: the
components `(id_{n+1}, h_{n+1})` of `TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`
with algebra inputs are `(0, h_{n+1})`. -/
theorem Homotopy.IsStrictlyUnital.toConeHom [CharP R 2]
    {f g : UngradedAInfinityRightModuleHom Mm Mm'} {H : Homotopy f g}
    (hH : H.IsStrictlyUnital ι) : H.toConeHom.IsStrictlyUnital ι :=
  fun _ _ i _ hi => LinearMap.ext fun m => by
    simp [hH.map_eq_zero hi, id_map_eq_zero i.pos.ne']

end StrictUnit

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

/-- A chain map of differential modules, viewed as a morphism of `A∞` modules, is strictly unital
for every family of elements of the algebra. -/
theorem isStrictlyUnital_toUngradedAInfinityRightModuleHom [CharP R 2] {S : Type*} {ι : S → A}
    (hM : IsUngradedDGRightModule d dM) (hM' : IsUngradedDGRightModule d dM')
    (g : M →ₗ[Aᵐᵒᵖ] M') (hg : ∀ m, g (dM m) = dM' (g m)) :
    (toUngradedAInfinityRightModuleHom hM hM' g hg).IsStrictlyUnital ι :=
  UngradedAInfinityRightModuleHom.isStrictlyUnital_of_map_add_one_eq_zero
    (toUngradedAInfinityRightModuleHom_map_add_one hM hM' g hg)

end IsUngradedDGRightModule

end TauCeti
