/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Surface
import TauCeti.GroupTheory.Perm.WreathProduct.Basic
import TauCeti.GroupTheory.SurfaceGroup.Closed
import Mathlib.Algebra.BigOperators.Pi

/-!
# Standard quadratic words are not conjugate to coefficients

By [IFT], §2.7, Lemma 1, a strictly quadratic word of `G[X] = G ∗ F(X)` is carried to a
standard quadratic word by an automorphism of `G[X]` fixing `G`. As stated this fails for the
coefficients and their conjugates, such as the strictly quadratic word `z⁻¹ c z`: the reduction
ends, after a conjugation, either at a coefficient `c ∈ G` or at a standard quadratic word. This
file shows that the two alternatives exclude each other: no standard quadratic word is conjugate
in `G[X]` to a coefficient, the trivial coefficient included
(`TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_inl`). Consequently a conjugate
`v⁻¹ c v` of a coefficient is not carried to a standard quadratic word by any homomorphism fixing
`c` followed by a conjugation (`Standard.toWord_ne_conj_map_conj_inl`). For `z⁻¹ c z` with
`c ≠ 1` this shows that the coefficient alternative cannot be avoided.

A conjugate of a coefficient is detected by two homomorphisms.

* Killing the coefficients sends a conjugate of a coefficient to `1`, and a standard word of
  positive genus `n` to `∏ᵢ [xᵢ, yᵢ]` or to `∏ᵢ xᵢ²`. Sending these variables to the generators
  of the closed surface group of genus `n` and the other variables to `1` gives the relator of
  that surface group in the free group on its generators, which is nontrivial
  (`TauCeti.SurfaceGroup.orientableRelator_ne_one`,
  `TauCeti.SurfaceGroup.nonorientableRelator_ne_one`).
* The words of genus zero, `z₁⁻¹ c₁ z₁ ⋯ z_m⁻¹ c_m z_m d` with `m ≥ 1` and nontrivial `cⱼ` and
  `d`, lie in the normal closure of `G`. Here `G[X]` is mapped to the regular wreath product
  `G ≀ F(X) = (F(X) → G) ⋊ F(X)`, sending a coefficient `g` to the function with the single
  nontrivial value `g` at `1` and a variable to itself in `F(X)`. A conjugate of a coefficient
  goes to a function with at most one nontrivial value, whereas the word above goes to the
  function with the value `d` at `1` and the value `c₁` at `z₁⁻¹`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_inl`: a standard quadratic word is not
  conjugate to a coefficient.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_map_conj_inl`: a homomorphism fixing a
  coefficient and a conjugation do not carry a conjugate of that coefficient to a standard
  quadratic word.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 3 and Lemma 1.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

open SurfaceGroup

variable {G X : Type*} [Group G]

/-! ### Positive genus -/

/-- Sending `xᵢ ↦ aᵢ`, `yᵢ ↦ bᵢ` and the other variables to `1`, the surface word
`∏ᵢ [xᵢ, yᵢ]` with trivial boundary elements goes to the relator of the closed surface group
`S⁺(n, 0)`, which is nontrivial. -/
private theorem exists_orientableWord_ne_one {n : ℕ} (hn : 0 < n) {x y : Fin n → X}
    (inj : (Sum.elim x y).Injective) : ∃ v : X → FreeGroup (OrientableGenerator n 0), ∀ m,
      orientableWord (fun i => v (x i)) (fun i => v (y i)) (fun _ : Fin m => 1) ≠ 1 := by
  let v : X → FreeGroup (OrientableGenerator n 0) :=
    Function.extend (Sum.elim x y) (fun s => .of (Sum.elim .a .b s)) 1
  have hx (i : Fin n) : v (x i) = .of (.a i) := inj.extend_apply _ _ (.inl i)
  have hy (i : Fin n) : v (y i) = .of (.b i) := inj.extend_apply _ _ (.inr i)
  refine ⟨v, fun m => ?_⟩
  simp only [hx, hy]
  convert orientableRelator_ne_one (g := n) (m := 0) (Or.inl hn.ne') using 1
  simp [orientableRelator_def, orientableWord_def, List.ofFn_const]

/-- Sending `xᵢ ↦ cᵢ` and the other variables to `1`, the surface word `∏ᵢ xᵢ²` with trivial
boundary elements goes to the relator of the closed surface group `S⁻(n, 0)`, which is
nontrivial. -/
private theorem exists_nonorientableWord_ne_one {n : ℕ} (hn : 0 < n) {x : Fin n → X}
    (inj : x.Injective) : ∃ v : X → FreeGroup (NonorientableGenerator n 0), ∀ m,
      nonorientableWord (fun i => v (x i)) (fun _ : Fin m => 1) ≠ 1 := by
  refine ⟨Function.extend x (fun i => .of (.c i)) 1, fun m => ?_⟩
  simp only [inj.extend_apply]
  convert nonorientableRelator_ne_one (g := n) (m := 0) (Or.inl hn.ne') using 1
  simp [nonorientableRelator_def, nonorientableWord_def, List.ofFn_const]

/-- A standard quadratic word of positive genus has a nontrivial value at some point of a group
over the trivial homomorphism of the coefficients. -/
private theorem exists_eval_one_toWord_ne_one {S : Standard G X} (hS : 0 < S.genus) :
    ∃ (K : Type) (_ : Group K) (v : X → K), eval (1 : G →* K) v S.toWord ≠ 1 := by
  cases S with
  | orientable n hn x y inj =>
    obtain ⟨v, hv⟩ := exists_orientableWord_ne_one hn inj
    refine ⟨_, inferInstance, v, ?_⟩
    rw [eval_toWord_orientable, Subsingleton.elim Fin.elim0 fun _ => 1]
    exact hv 0
  | orientableCoeff n m hnm x y z inj =>
    obtain ⟨v, hv⟩ := exists_orientableWord_ne_one (by simpa using hS) (Sum.elim_injective.1 inj).1
    refine ⟨_, inferInstance, v, ?_⟩
    simpa [orientableWord_snoc] using hv m
  | nonorientable n hn x inj =>
    obtain ⟨v, hv⟩ := exists_nonorientableWord_ne_one hn inj
    refine ⟨_, inferInstance, v, ?_⟩
    rw [eval_toWord_nonorientable, Subsingleton.elim Fin.elim0 fun _ => 1]
    exact hv 0
  | nonorientableCoeff n m hn x z inj =>
    obtain ⟨v, hv⟩ := exists_nonorientableWord_ne_one hn (Sum.elim_injective.1 inj).1
    refine ⟨_, inferInstance, v, ?_⟩
    simpa [nonorientableWord_snoc] using hv m

/-! ### Genus zero: the regular wreath product `G ≀ F(X)` -/

open Classical in
/-- The homomorphism from `G[X]` to the regular wreath product `G ≀ F(X)`, the permutation wreath
product `(F(X) → G) ⋊ F(X)` for the action of `F(X)` on itself by left multiplication: a
coefficient `g` goes to the function with the single nontrivial value `g` at `1`, and a variable
to itself in `F(X)`. -/
private noncomputable def toWreath :
    GX G X →* PermutationWreathProduct G (FreeGroup X) (FreeGroup X) :=
  eval (SemidirectProduct.inl.comp (MonoidHom.mulSingle (fun _ : FreeGroup X => G) 1))
    fun x => .inr (.of x)

open Classical in
private theorem toWreath_inl (g : G) : toWreath (inl g : GX G X) = .inl (Pi.mulSingle 1 g) := by
  simp [toWreath]

private theorem toWreath_inr_of (x : X) :
    toWreath (inr (FreeGroup.of x) : GX G X) = .inr (FreeGroup.of x) := by
  simp [toWreath]

open Classical in
/-- The conjugate `z⁻¹ c z` goes to the function with the single nontrivial value `c` at
`z⁻¹`. -/
private theorem toWreath_inv_mul_inl_mul (z : X) (c : G) :
    toWreath ((inr (FreeGroup.of z))⁻¹ * inl c * inr (FreeGroup.of z) : GX G X) =
      .inl (Pi.mulSingle (FreeGroup.of z)⁻¹ c) := by
  ext p
  · simp [toWreath_inl, toWreath_inr_of, Pi.mulSingle_apply, eq_inv_iff_mul_eq_one,
      mul_eq_one_comm]
  · simp [toWreath_inl, toWreath_inr_of]

/-- The image of a conjugate `u g u⁻¹` of a coefficient has at most one nontrivial value, at the
top component of the image of `u`. -/
private theorem eq_toWreath_right_of_toWreath_conj_inl_ne_one {u : GX G X} {g : G} {p : FreeGroup X}
    (hp : (toWreath (u * inl g * u⁻¹)).left p ≠ 1) : p = (toWreath u).right := by
  classical
  by_contra hne
  exact hp (by simp [toWreath_inl, inv_mul_eq_one, Ne.symm hne])

/-- A standard quadratic word of genus zero, `z₁⁻¹ c₁ z₁ ⋯ z_m⁻¹ c_m z_m d`, is not conjugate to
a coefficient. -/
private theorem toWord_orientableCoeff_zero_ne_conj_inl {m : ℕ} (hnm : 0 < 0 + m) {x y : Fin 0 → X}
    {z : Fin m → X} (inj : (Sum.elim (Sum.elim x y) z).Injective) {c : Fin m → G}
    (hc : ∀ j, c j ≠ 1) {d : G} (hd : d ≠ 1) (u : GX G X) (g : G) :
    (orientableCoeff 0 m hnm x y z inj c hc d hd).toWord ≠ u * inl g * u⁻¹ := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  have hw : toWreath (orientableCoeff 0 (k + 1) hnm x y z inj c hc d hd).toWord =
      .inl ((List.ofFn fun j => Pi.mulSingle (FreeGroup.of (z j))⁻¹ (c j)).prod *
        Pi.mulSingle 1 d) := by
    simp only [toWord_def, atoms_orientableCoeff, List.ofFn_zero, List.nil_append, map_mul,
      map_list_prod, List.map_ofFn, constant_orientableCoeff, toWreath_inl]
    congr 3
    funext j
    exact toWreath_inv_mul_inl_mul (z j) (c j)
  intro h
  -- The image of the word has the nontrivial values `d` at `1` and `c₁` at `z₁⁻¹`.
  have h1 := eq_toWreath_right_of_toWreath_conj_inl_ne_one (u := u) (g := g) (p := 1) (by
    simpa [← h, hw, Pi.list_prod_apply, Pi.mulSingle_apply, Function.comp_def,
      eq_comm (a := 1), FreeGroup.of_ne_one])
  have h2 := eq_toWreath_right_of_toWreath_conj_inl_ne_one (u := u) (g := g)
    (p := (FreeGroup.of (z 0))⁻¹) (by
    simpa [← h, hw, Pi.list_prod_apply, Pi.mulSingle_apply, Function.comp_def,
      FreeGroup.of_ne_one, List.ofFn_succ, FreeGroup.of_injective.eq_iff,
      (Sum.elim_injective.1 inj).2.1.eq_iff,
      eq_comm (a := (0 : Fin (k + 1)))] using hc 0)
  exact FreeGroup.of_ne_one (z 0) (inv_eq_one.1 (h2.trans h1.symm))

/-! ### Standard quadratic words and coefficients -/

/-- **A standard quadratic word is not conjugate to a coefficient**, the trivial coefficient
included. Hence the two possible outcomes of reducing a strictly quadratic word by automorphisms
of `G[X]` fixing `G` and conjugations, a coefficient or a standard quadratic word, exclude each
other. -/
theorem toWord_ne_conj_inl (S : Standard G X) (u : GX G X) (g : G) :
    S.toWord ≠ u * inl g * u⁻¹ := by
  intro h
  by_cases hS : 0 < S.genus
  · obtain ⟨K, _, v, hv⟩ := exists_eval_one_toWord_ne_one hS
    exact hv (by simp [h])
  -- The genus is positive in the types (1), (3), (4); a word of genus zero is of type (2).
  cases S with
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    obtain rfl : n = 0 := by simpa using hS
    exact toWord_orientableCoeff_zero_ne_conj_inl hnm inj hc hd u g h
  | _ => simp_all

/-- A homomorphism `G[Y] → G[X]` fixing the coefficient `c`, followed by a conjugation, does not
carry a conjugate `v⁻¹ c v` of `c` to a standard quadratic word. For instance the strictly
quadratic word `z⁻¹ c z` is not brought to a standard quadratic word by a change of coordinates
over `G` and a conjugation. -/
theorem toWord_ne_conj_map_conj_inl {Y : Type*} (S : Standard G X) {f : GX G Y →* GX G X} {c : G}
    (hf : f (inl c) = inl c) (u : GX G X) (v : GX G Y) :
    S.toWord ≠ u * f (v⁻¹ * inl c * v) * u⁻¹ := by
  simpa [hf, mul_assoc] using S.toWord_ne_conj_inl (u * (f v)⁻¹) c

end TauCeti.GroupAlgGeom.Quadratic.Standard
