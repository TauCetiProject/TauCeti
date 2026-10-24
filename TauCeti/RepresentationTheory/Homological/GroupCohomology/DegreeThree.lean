/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Group `3`-cocycles

Mathlib's specialised low-degree API for the inhomogeneous cochain complex of a representation
`A : Rep k G` stops at the `2`-cocycles `groupCohomology.cocycles₂`. This file continues it one
degree further: it identifies the differential `C³(G, A) ⟶ C⁴(G, A)` of
`groupCohomology.inhomogeneousCochains A` with an explicit map
`TauCeti.groupCohomology.d₃₄ : Fun(G³, A) ⟶ Fun(G⁴, A)`, and defines the `3`-cocycles and
`3`-coboundaries as submodules of `Fun(G³, A)`, the former being the functions whose inhomogeneous
cochain is killed by the general differential.

Degree-three cocycles with values in a multiplicative group are the associativity data of pointed
tensor categories: a normalized `3`-cocycle `ω : G × G × G → kˣ` for the trivial action is exactly
what twists the associator of `G`-graded vector spaces, the cocycle identity being the pentagon
axiom and normalization making the unitors trivial. For this the file provides, as Mathlib does in
degrees `1` and `2`, the unbundled multiplicative predicates `IsMulCocycle₃` and
`IsMulCoboundary₃` for a group `M` with an action of `G`, their comparison with the submodules
above for `Rep.ofMulDistribMulAction G M`, and the normalization theory: the values of a
`3`-cocycle with an argument equal to `1` are determined by its values at `(g, 1, 1)` and
`(1, 1, j)`, and every `3`-cocycle is cohomologous to a normalized one, that is, one taking the
value `1` whenever an argument is `1`.

## Main definitions

* `TauCeti.groupCohomology.d₃₄`: the third inhomogeneous differential, as a `k`-linear map
  `Fun(G³, A) ⟶ Fun(G⁴, A)`, with `TauCeti.groupCohomology.comp_d₃₄_eq` identifying it with
  `(inhomogeneousCochains A).d 3 4`.
* `TauCeti.groupCohomology.cocycles₃`, `TauCeti.groupCohomology.coboundaries₃`: the `3`-cocycles
  and `3`-coboundaries of `A`.
* `TauCeti.groupCohomology.IsMulCocycle₃`, `TauCeti.groupCohomology.IsMulCoboundary₃`: the
  multiplicative `3`-cocycle and `3`-coboundary conditions.

## Main statements

* `TauCeti.groupCohomology.mem_cocycles₃_iff`: the `3`-cocycle identity
  `f(gh, j, l) + f(g, h, jl) = g • f(h, j, l) + f(g, hj, l) + f(g, h, j)`.
* `TauCeti.groupCohomology.mem_cocycles₃_iff_d_cochainsIso₃_inv_eq_zero`: the `3`-cocycles are
  the kernel of the differential `d 3 4` of `inhomogeneousCochains A`.
* `TauCeti.groupCohomology.mem_cocycles₃_ofMulDistribMulAction_iff`: the multiplicative
  `3`-cocycles are the `3`-cocycles of `Rep.ofMulDistribMulAction G M`.
* `TauCeti.groupCohomology.IsMulCoboundary₃.isMulCocycle₃`: multiplicative `3`-coboundaries are
  `3`-cocycles.
* `TauCeti.groupCohomology.exists_normalized_of_isMulCocycle₃`: every multiplicative `3`-cocycle
  differs by a `3`-coboundary from a normalized one.

## References

* `Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` (Amelia Livingston,
  Joël Riou), whose degree-`2` declarations `d₂₃`, `cochainsIso₃`, `comp_d₂₃_eq`, `cocycles₂` and
  `IsMulCocycle₂` the declarations here extend, in the same shape
* K. S. Brown, *Cohomology of groups*, Graduate Texts in Mathematics 87, Springer, 1982, §I.5
  (the standard resolution and its normalized form)
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.3
  (the categories `Vec^ω_G`)
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace TauCeti.groupCohomology

open _root_.groupCohomology

section Rep

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- The 4th object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G⁴, A)` as a `k`-module. -/
def cochainsIso₄ : (inhomogeneousCochains A).X 4 ≅ ↧(G × G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A ((Fin.consEquiv _).symm.trans ((Equiv.refl G).prodCongr
    ((Fin.consEquiv _).symm.trans ((Equiv.refl G).prodCongr
      (piFinTwoEquiv fun _ => G)))))).toModuleIso.symm

/-- The 3rd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G³, A) → Fun(G⁴, A)`. It sends `(f, (g₁, g₂, g₃, g₄))` to
`ρ_A(g₁)(f(g₂, g₃, g₄)) - f(g₁g₂, g₃, g₄) + f(g₁, g₂g₃, g₄) - f(g₁, g₂, g₃g₄) + f(g₁, g₂, g₃)`. -/
@[simps!]
def d₃₄ : ModuleCat.of k (G × G × G → A) ⟶ ModuleCat.of k (G × G × G × G → A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f (g.2.1, g.2.2.1, g.2.2.2)) - f (g.1 * g.2.1, g.2.2.1, g.2.2.2) +
        f (g.1, g.2.1 * g.2.2.1, g.2.2.2) - f (g.1, g.2.1, g.2.2.1 * g.2.2.2) +
        f (g.1, g.2.1, g.2.2.1)
    map_add' x y := funext fun g => by
      simp only [Pi.add_apply, map_add]
      abel
    map_smul' r x := funext fun g => by
      simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, smul_sub] }

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d₃₄` gives a simpler expression for the 3rd differential: that is, the following
square commutes:
```
        C³(G, A) -------d 3 4-------> C⁴(G, A)
          |                              |
          v                              v
  Fun(G × G × G, A) --d₃₄--> Fun(G × G × G × G, A)
```
where the vertical arrows are `cochainsIso₃` and `cochainsIso₄` respectively.
-/
theorem comp_d₃₄_eq :
    (cochainsIso₃ A).hom ≫ d₃₄ A =
      (inhomogeneousCochains A).d 3 4 ≫ (cochainsIso₄ A).hom := by
  ext x y
  -- unfold `d₃₄` to its five terms, so that they can be matched with the inhomogeneous sum
  change A.ρ y.1 (x _) - x _ + x _ - x _ + x _ = _ + _
  have h : (-1 : k) ^ (((3 : Fin 4) : ℕ) + 1) = 1 := by norm_num
  dsimp
  rw [Fin.sum_univ_four, h]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow,
    mul_one]
  rcongr i <;> fin_cases i <;> rfl

/-- The square of `comp_d₃₄_eq`, read with the inverses of the vertical isomorphisms. -/
@[reassoc, elementwise]
theorem eq_d₃₄_comp_inv :
    (cochainsIso₃ A).inv ≫ (inhomogeneousCochains A).d 3 4 =
      d₃₄ A ≫ (cochainsIso₄ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₃₄_eq A⟩).w

/-- Consecutive differentials compose to zero: `d₂₃ ≫ d₃₄ = 0`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₂₃_comp_d₃₄ : d₂₃ A ≫ d₃₄ A = 0 := by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

/-- The 3-cocycles `Z³(G, A)` of `A : Rep k G`, defined as the kernel of the map
`d₃₄ : Fun(G × G × G, A) → Fun(G × G × G × G, A)`. -/
def cocycles₃ : Submodule k (G × G × G → A) := LinearMap.ker (d₃₄ A).hom

/-- The 3-coboundaries `B³(G, A)` of `A : Rep k G`, defined as the image of the map
`d₂₃ : Fun(G × G, A) → Fun(G × G × G, A)`. -/
def coboundaries₃ : Submodule k (G × G × G → A) := LinearMap.range (d₂₃ A).hom

variable {A}

/-- The `3`-cocycle identity, as the vanishing of the alternating sum defining `d₃₄`. -/
theorem mem_cocycles₃_def (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ ∀ g h j l : G,
      A.ρ g (f (h, j, l)) - f (g * h, j, l) + f (g, h * j, l) - f (g, h, j * l) + f (g, h, j) =
        0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, d₃₄_hom_apply, Prod.forall]
    rfl

/-- The `3`-cocycle identity, with the terms of each sign collected on one side. -/
theorem mem_cocycles₃_iff (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ ∀ g h j l : G,
      f (g * h, j, l) + f (g, h, j * l) = A.ρ g (f (h, j, l)) + f (g, h * j, l) + f (g, h, j) := by
  refine (mem_cocycles₃_def f).trans (forall₄_congr fun g h j l => ?_)
  rw [← neg_eq_zero, ← sub_eq_zero (a := f (g * h, j, l) + _)]
  constructor <;> intro H <;> rw [← H] <;> abel

/-- A function is a `3`-coboundary when it is the image under `d₂₃` of some `2`-cochain. -/
theorem mem_coboundaries₃_iff (f : G × G × G → A) :
    f ∈ coboundaries₃ A ↔ ∃ x : G × G → A, ∀ g h j : G,
      A.ρ g (x (h, j)) - x (g * h, j) + x (g, h * j) - x (g, h) = f (g, h, j) := by
  simp_rw [coboundaries₃, LinearMap.mem_range, funext_iff, d₂₃_hom_apply, Prod.forall]

variable (A)

/-- The image of a `2`-cochain under `d₂₃` is a `3`-cocycle. -/
theorem d₂₃_apply_mem_cocycles₃ (x : G × G → A) : d₂₃ A x ∈ cocycles₃ A :=
  d₂₃_comp_d₃₄_apply _ _

/-- Every `3`-coboundary is a `3`-cocycle. -/
theorem coboundaries₃_le_cocycles₃ : coboundaries₃ A ≤ cocycles₃ A := by
  rintro _ ⟨x, rfl⟩
  exact d₂₃_apply_mem_cocycles₃ A x

/-- A function `f : Fun(G³, A)` is a `3`-cocycle exactly when the corresponding inhomogeneous
cochain is killed by the differential `d 3 4` of `inhomogeneousCochains A`. -/
theorem mem_cocycles₃_iff_d_cochainsIso₃_inv_eq_zero (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ (inhomogeneousCochains A).d 3 4 ((cochainsIso₃ A).inv f) = 0 := by
  rw [eq_d₃₄_comp_inv_apply, cocycles₃, LinearMap.mem_ker]
  exact (map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)).symm

end Rep

/-! ### Multiplicative `3`-cocycles -/

section IsMulCocycle₃

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G × G × G → M` satisfies the multiplicative 3-cocycle condition if
`f(gh, j, l) * f(g, h, jl) = g • f(h, j, l) * f(g, hj, l) * f(g, h, j)` for all `g, h, j, l : G`.
For the trivial action of `G` on `M` this is the pentagon identity for the associator of the
category of `G`-graded vector spaces twisted by `f`. -/
def IsMulCocycle₃ (f : G × G × G → M) : Prop :=
  ∀ g h j l : G,
    f (g * h, j, l) * f (g, h, j * l) = g • f (h, j, l) * f (g, h * j, l) * f (g, h, j)

/-- A function `f : G × G × G → M` satisfies the multiplicative 3-coboundary condition if there is
`x : G × G → M` such that `g • x(h, j) / x(gh, j) * x(g, hj) / x(g, h) = f(g, h, j)` for all
`g, h, j : G`. -/
def IsMulCoboundary₃ (f : G × G × G → M) : Prop :=
  ∃ x : G × G → M, ∀ g h j : G, g • x (h, j) / x (g * h, j) * x (g, h * j) / x (g, h) = f (g, h, j)

end IsMulCocycle₃

section ofMulDistribMulAction

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- A function into `M` is a multiplicative 3-cocycle exactly when, viewed in `Additive M`, it is a
3-cocycle of the representation `Rep.ofMulDistribMulAction G M`. -/
theorem mem_cocycles₃_ofMulDistribMulAction_iff (f : G × G × G → M) :
    Additive.ofMul ∘ f ∈ cocycles₃ (Rep.ofMulDistribMulAction G M) ↔ IsMulCocycle₃ f :=
  mem_cocycles₃_iff (A := Rep.ofMulDistribMulAction G M) f

/-- A function into `M` is a multiplicative 3-coboundary exactly when, viewed in `Additive M`, it
is a 3-coboundary of the representation `Rep.ofMulDistribMulAction G M`. -/
theorem mem_coboundaries₃_ofMulDistribMulAction_iff (f : G × G × G → M) :
    Additive.ofMul ∘ f ∈ coboundaries₃ (Rep.ofMulDistribMulAction G M) ↔ IsMulCoboundary₃ f :=
  (mem_coboundaries₃_iff (A := Rep.ofMulDistribMulAction G M) _).trans
    ⟨fun ⟨x, hx⟩ => ⟨Additive.toMul ∘ x, hx⟩, fun ⟨x, hx⟩ => ⟨Additive.ofMul ∘ x, hx⟩⟩

end ofMulDistribMulAction

section Monoid

variable {G M : Type*} [Monoid G] [CommGroup M]

section MulAction

variable [MulAction G M] {f : G × G × G → M}

/-- The value of a multiplicative 3-cocycle at `(1, h, j)` is determined by its values at
`(1, 1, -)`. -/
theorem map_one_fst_of_isMulCocycle₃ (hf : IsMulCocycle₃ f) (h j : G) :
    f (1, h, j) = f (1, 1, h * j) / f (1, 1, h) := by
  have := hf 1 1 h j
  simp only [one_mul, one_smul] at this
  rw [eq_div_iff_mul_eq', ← mul_right_inj (f (1, h, j)), this, mul_assoc]

/-- The value of a multiplicative 3-cocycle at `(g, 1, j)` is determined by its values at
`(1, 1, j)` and `(g, 1, 1)`. -/
theorem map_one_snd_of_isMulCocycle₃ (hf : IsMulCocycle₃ f) (g j : G) :
    f (g, 1, j) = g • f (1, 1, j) * f (g, 1, 1) := by
  have := hf g 1 1 j
  simp only [mul_one, one_mul] at this
  rwa [mul_right_comm _ (f (g, 1, j)), mul_left_inj] at this

/-- The value of a multiplicative 3-cocycle at `(g, h, 1)` is determined by its values at
`(-, 1, 1)`. -/
theorem map_one_thd_of_isMulCocycle₃ (hf : IsMulCocycle₃ f) (g h : G) :
    f (g, h, 1) = f (g * h, 1, 1) / g • f (h, 1, 1) := by
  have := hf g h 1 1
  simp only [mul_one] at this
  rw [mul_left_inj] at this
  rw [this, mul_div_cancel_left]

/-- A multiplicative 3-cocycle takes the value `1` at `(1, 1, 1)`. -/
theorem map_one_one_one_of_isMulCocycle₃ (hf : IsMulCocycle₃ f) : f (1, 1, 1) = 1 := by
  simpa using map_one_snd_of_isMulCocycle₃ hf 1 1

end MulAction

variable [MulDistribMulAction G M] {f f' : G × G × G → M}

/-- A multiplicative 3-cocycle is normalized, in the sense that it takes the value `1` whenever an
argument is `1`, as soon as it takes the value `1` at all `(g, 1, j)`. -/
theorem map_eq_one_of_isMulCocycle₃ (hf : IsMulCocycle₃ f) (h1 : ∀ g j : G, f (g, 1, j) = 1)
    {g h j : G} (hghj : g = 1 ∨ h = 1 ∨ j = 1) : f (g, h, j) = 1 := by
  rcases hghj with rfl | rfl | rfl
  · rw [map_one_fst_of_isMulCocycle₃ hf, h1, h1, div_one]
  · exact h1 g j
  · rw [map_one_thd_of_isMulCocycle₃ hf, h1, h1, smul_one, div_one]

/-- The constant function `1` is a multiplicative 3-cocycle. -/
theorem isMulCocycle₃_one : IsMulCocycle₃ (1 : G × G × G → M) := by
  intro g h j l
  simp

/-- The pointwise product of multiplicative 3-cocycles is a 3-cocycle. -/
theorem IsMulCocycle₃.mul (hf : IsMulCocycle₃ f) (hf' : IsMulCocycle₃ f') :
    IsMulCocycle₃ (f * f') := by
  intro g h j l
  simp only [Pi.mul_apply, smul_mul']
  rw [mul_mul_mul_comm, hf, hf']
  simp only [mul_mul_mul_comm]

/-- The pointwise inverse of a multiplicative 3-cocycle is a 3-cocycle. -/
theorem IsMulCocycle₃.inv (hf : IsMulCocycle₃ f) : IsMulCocycle₃ f⁻¹ := by
  intro g h j l
  simp only [Pi.inv_apply, smul_inv', ← mul_inv]
  rw [hf]

/-- The pointwise quotient of multiplicative 3-cocycles is a 3-cocycle. -/
theorem IsMulCocycle₃.div (hf : IsMulCocycle₃ f) (hf' : IsMulCocycle₃ f') :
    IsMulCocycle₃ (f / f') := by
  rw [div_eq_mul_inv]
  exact hf.mul hf'.inv

/-- A multiplicative 3-coboundary is a 3-cocycle. -/
theorem IsMulCoboundary₃.isMulCocycle₃ (hf : IsMulCoboundary₃ f) : IsMulCocycle₃ f := by
  obtain ⟨x, hx⟩ := hf
  intro g h j l
  simp only [← hx, smul_div', smul_mul', smul_smul, mul_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

/-- **Normalization of 3-cocycles.** Every multiplicative 3-cocycle `f` differs by a 3-coboundary
from a 3-cocycle `f'` that is normalized: `f' (g, h, j) = 1` whenever one of `g`, `h`, `j` is `1`.
-/
theorem exists_normalized_of_isMulCocycle₃ (hf : IsMulCocycle₃ f) :
    ∃ f' : G × G × G → M, IsMulCocycle₃ f' ∧ IsMulCoboundary₃ (f / f') ∧
      ∀ g h j : G, g = 1 ∨ h = 1 ∨ j = 1 → f' (g, h, j) = 1 := by
  -- the coboundary of the 2-cochain `x (g, h) = f (1, 1, h) / f (g, 1, 1)` agrees with `f` on
  -- every `(g, 1, j)`, so dividing it out leaves a cocycle that is `1` there
  let x : G × G → M := fun a => f (1, 1, a.2) / f (a.1, 1, 1)
  let b : G × G × G → M := fun a =>
    a.1 • x (a.2.1, a.2.2) / x (a.1 * a.2.1, a.2.2) * x (a.1, a.2.1 * a.2.2) / x (a.1, a.2.1)
  have hb : IsMulCoboundary₃ b := ⟨x, fun _ _ _ => rfl⟩
  have hf' : IsMulCocycle₃ (f / b) := hf.div hb.isMulCocycle₃
  refine ⟨f / b, hf', ⟨x, fun g h j => ?_⟩, fun g h j hghj =>
    map_eq_one_of_isMulCocycle₃ hf' (fun g j => ?_) hghj⟩
  · simp only [Pi.div_apply, div_div_cancel, b]
  · have h111 := map_one_one_one_of_isMulCocycle₃ hf
    simp only [Pi.div_apply, b, x, one_mul, mul_one, h111, div_one, one_div, smul_div',
      smul_one, div_mul_cancel, map_one_snd_of_isMulCocycle₃ hf g j, div_inv_eq_mul, div_self']

end Monoid

end TauCeti.groupCohomology
