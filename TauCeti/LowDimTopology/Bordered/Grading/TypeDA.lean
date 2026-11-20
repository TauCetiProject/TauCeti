/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Matrix.Grading
public import TauCeti.LowDimTopology.Bordered.TypeDA
import TauCeti.Algebra.Group.Action.Pow
import Mathlib.Tactic.Group

/-!
# Gradings of type `DA` bimodules and of their box tensor products with type `D` structures

The bordered algebras of Lipshitz, Ozsváth and Thurston are graded by nonabelian groups with
distinguished central elements, and a type `DA` bimodule `^B P_A` is graded by a set carrying a
left action of the grading group `G_B` of `B` and a right action of the grading group `G_A` of
`A`. This file grades the type `DA` bimodules of `TauCeti.LowDimTopology.Bordered.TypeDA` and shows
that the box tensor product `P ⊠ N` with a graded type `D` structure `N` over `A` is a graded type
`D` structure over `B`, with structure map of the same degree. It extends the gradings of type `D`
structures (`TauCeti.LowDimTopology.Bordered.Grading.Basic`), whose structure map plays the role of
the operation `δ¹₁` of a bimodule.

As there, the algebras are graded by families of submodules `Ag : G_A → Submodule R A` and
`Bg : G_B → Submodule R B`, and `l` is the degree of the differentials (`λ⁻¹` in the bordered
algebras). The right action of `G_A` on the grading set `U` of `P` is written as a left action of
the opposite group `G_Aᵐᵒᵖ`, `u · g = op g • u`. Unlike the inverse convention `s · g = g⁻¹ • s`
used for type `A` modules, this lets `U` carry both actions when `G_A = G_B`, as for the identity
bimodule.

* **Graded type `DA` bimodules.** A bimodule with generators `y : Y` is graded by `gr : Y → U`
  (`TauCeti.TypeDAStructure.IsGraded`) when its operation `δ¹_{n+1}` has degree
  `λ^{n-1} = l^{1-n}`: for inputs `aᵢ` of degrees `gᵢ`, each coefficient of
  `δ¹_{n+1}(y, a₁, …, aₙ) = ∑ y', b ⊗ y'` is a sum of elements `b` of degrees `h` with
  `h • gr y' = l^{1-n} • gr y · (g₁ ⋯ gₙ)`. So `δ¹₁` has degree `l`, as the structure map of a type
  `D` structure (`TauCeti.TypeDAStructure.IsGraded.coeff_zero_mem`), and `δ¹₂` is graded with no
  shift (`TauCeti.TypeDAStructure.IsGraded.coeff_one_mem`). The identity bimodule `[I]` is graded
  by the regular `G`-biset `G`, every generator in degree `1`
  (`TauCeti.TypeDAStructure.isGraded_identity`).
* **Box tensor products.** Let `N` be a type `D` structure over `A` with generators graded by a
  left `G_A`-set `T` and structure map of central degree `l_A`. The generators `y ⊗ x` of `P ⊠ N`
  are graded by `π (gr y) (gr x)` for any map `π : U → T → V` into a left `G_B`-set `V` that is
  balanced, `π (u · g) t = π u (g • t)`, equivariant, `π (h • u) t = h • π u t`, and identifies the
  central elements, `π u (l_A • t) = l • π u t`. When the two actions on `U` commute and
  `u · l_A = l • u`, as for the bimodule grading sets of Lipshitz, Ozsváth and Thurston, the
  quotient of `U × T` by `(u · g, t) ∼ (u, g • t)`, the balanced product `U ×_{G_A} T`, is such a
  map, through which the others factor. Then the structure map of
  `P ⊠ N` has degree `l` (`TauCeti.TypeDAStructure.IsGraded.boxCoeff_mem_homogeneousMatrices`):
  along a path of `k` coefficients of `N`, the degrees multiply to `l_A^k`, and `δ¹_{k+1}` has
  degree `l^{1-k}`. No boundedness is needed: an infinite sum is `0` by the convention of
  `TauCeti.TypeDAStructure.boxCoeff`.

## Main definitions

* `TauCeti.TypeDAStructure.IsGraded`: a type `DA` bimodule graded by a set with a left `G_B` action
  and a right `G_A` action, with `δ¹_{n+1}` of degree `λ^{n-1}`.

## Main results

* `TauCeti.TypeDAStructure.IsGraded.coeff_zero_mem` and
  `TauCeti.TypeDAStructure.IsGraded.coeff_one_mem`: the degrees of `δ¹₁` and `δ¹₂`.
* `TauCeti.TypeDAStructure.isGraded_identity`: the grading of the identity bimodule.
* `TauCeti.TypeDAStructure.IsGraded.boxCoeff_mem_homogeneousMatrices`: the structure map of the box
  tensor product of a graded type `DA` bimodule with a graded type `D` structure is homogeneous.
* `TauCeti.TypeDAStructure.boxCoeff_identity_mem_homogeneousMatrices`: `[I] ⊠ N` is graded as `N`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §2.5
  (gradings by a group with a distinguished central element, of type `D` structures by `G`-sets,
  and of box tensor products by balanced products of grading sets).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), Section 2
  (gradings of type `DA` bimodules by sets with commuting left and right actions, and of their box
  tensor products).
-/

public section

open MulOpposite

namespace TauCeti

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {GA GB : Type*} [Group GA] [Group GB] {Ag : GA → Submodule R A} {Bg : GB → Submodule R B}
  {U : Type*} [MulAction GB U] [MulAction GAᵐᵒᵖ U]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S : Type*} {ιB : S → B} {Y : Type*} [Fintype Y]

namespace TypeDAStructure

/-! ### Graded type `DA` bimodules -/

/-- A type `DA` bimodule `^B P_A` is **graded** by `gr : Y → U`, over the gradings `Ag` of `A` and
`Bg` of `B`, with differentials of degree `l` (`λ⁻¹` in the bordered algebras), when its operation
`δ¹_{n+1}` has degree `λ^{n-1} = l^{1-n}`: for inputs `aᵢ` of degrees `gᵢ`, the coefficient matrix
`δₙ(a₁, …, aₙ)` from `y` to `y'` is a sum of elements of the degrees `h` with
`h • gr y' = l^{1-n} • gr y · (g₁ ⋯ gₙ)`, where the right action of `G_A` is the action of the
opposite group, `u · g = op g • u`. -/
def IsGraded (P : TypeDAStructure dA dB ιB Y) (Ag : GA → Submodule R A)
    (Bg : GB → Submodule R B) (gr : Y → U) (l : GB) : Prop :=
  ∀ (n : ℕ) (g : Fin n → GA) (a : Fin n → A), (∀ i, a i ∈ Ag (g i)) →
    P.coeff n a ∈ homogeneousMatrices Bg (fun y ↦ op (List.ofFn g).prod • gr y) gr
      (l ^ (1 - (n : ℤ)))

variable {P : TypeDAStructure dA dB ιB Y} {gr : Y → U} {l : GB}

/-- The definition of a graded type `DA` bimodule, unfolded. -/
theorem isGraded_iff : P.IsGraded Ag Bg gr l ↔
    ∀ (n : ℕ) (g : Fin n → GA) (a : Fin n → A), (∀ i, a i ∈ Ag (g i)) →
      P.coeff n a ∈ homogeneousMatrices Bg (fun y ↦ op (List.ofFn g).prod • gr y) gr
        (l ^ (1 - (n : ℤ))) :=
  Iff.rfl

namespace IsGraded

/-- The operation `δ¹_{n+1}` of a graded type `DA` bimodule has degree `l^{1-n}`. -/
theorem coeff_mem (hP : P.IsGraded Ag Bg gr l) {n : ℕ} {g : Fin n → GA} {a : Fin n → A}
    (ha : ∀ i, a i ∈ Ag (g i)) :
    P.coeff n a ∈ homogeneousMatrices Bg (fun y ↦ op (List.ofFn g).prod • gr y) gr
      (l ^ (1 - (n : ℤ))) :=
  hP n g a ha

/-- The operation `δ¹₁` of a graded type `DA` bimodule has degree `l`, as the structure map of a
graded type `D` structure. -/
theorem coeff_zero_mem (hP : P.IsGraded Ag Bg gr l) (a : Fin 0 → A) :
    P.coeff 0 a ∈ homogeneousMatrices Bg gr gr l := by
  simpa using hP.coeff_mem (g := Fin.elim0) (a := a) fun i ↦ i.elim0

/-- The operation `δ¹₂` of a graded type `DA` bimodule is graded: for an input of degree `g`, the
coefficients from `y` to `y'` are sums of elements of the degrees `h` with
`h • gr y' = gr y · g`. -/
theorem coeff_one_mem (hP : P.IsGraded Ag Bg gr l) {a : Fin 1 → A} {g : GA}
    (ha : a 0 ∈ Ag g) : P.coeff 1 a ∈ homogeneousMatrices Bg (fun y ↦ op g • gr y) gr 1 := by
  simpa using hP.coeff_mem (n := 1) (g := fun _ ↦ g) fun i ↦ by rwa [Subsingleton.elim i 0]

end IsGraded

/-! ### The identity bimodule -/

section Identity

variable {G : Type*} [Group G] {Ag : G → Submodule R A} {d : A →ₗ[R] A} {ι : S → A} [Fintype S]
  [CharP R 2]

/-- **The grading of the identity bimodule.** Let `A` be graded by `Ag`, with
`Ag g * Ag h ⊆ Ag (g * h)` and idempotents of degree `1`. Then the identity bimodule `[I]` is
graded by the group `G`, with its left and right regular actions, every generator in degree `1`,
for any degree `l` of the differentials: its only operation `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t`
preserves degrees. -/
theorem isGraded_identity (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1)
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h))
    (hι1 : ∀ s, ι s ∈ Ag 1) (l : G) :
    (identity ι hd hι hιι hsum).IsGraded Ag Ag (fun _ ↦ (1 : G)) l := by
  intro n g a ha
  rcases eq_or_ne n 1 with rfl | hn
  · -- `ι s * a * ι t` has the degree `g 0` of `a`.
    refine mem_homogeneousMatrices_iff.mpr fun s t ↦ ?_
    rw [identity_coeff_one_apply]
    refine Submodule.mem_iSup_of_mem ⟨g 0, by simp⟩ ?_
    simpa using hA (hA (hι1 s) (ha 0)) (hι1 t)
  · rw [identity_coeff_eq_zero hd hι hιι hsum hn, zero_apply]
    exact zero_mem _

end Identity

/-! ### The box tensor product with a type `D` structure -/

section BoxTypeD

variable {K : Type*} {ιA : K → A} {X : Type*} [Fintype X] [DecidableEq X] {T : Type*}
  [MulAction GA T] {V : Type*} [MulAction GB V]

/-- **The box tensor product `P ⊠ N` of graded structures is graded.** Let `P` be a type `DA`
bimodule graded by `gr : Y → U` with differentials of degree `l`, and `N` a type `D` structure over
`A` whose structure map has central degree `l_A` for the grading `grN : X → T` by a left `G_A`-set.
Let `π : U → T → V` into a left `G_B`-set be balanced, `π (u · g) t = π u (g • t)`,
`G_B`-equivariant, and identify `l_A` with `l`, `π u (l_A • t) = l • π u t`; for instance the
quotient map to the balanced product `U ×_{G_A} T` when the actions on `U` commute and
`u · l_A = l • u`. Then the structure map of `P ⊠ N` has degree
`l` for the grading `(y, x) ↦ π (gr y) (grN x)` of its generators. -/
theorem IsGraded.boxCoeff_mem_homogeneousMatrices (hP : P.IsGraded Ag Bg gr l)
    {N : TypeDStructure dA ιA X} {lA : Subgroup.center GA} {grN : X → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag grN grN lA) {π : U → T → V}
    (hπA : ∀ (g : GA) u t, π (op g • u) t = π u (g • t))
    (hπB : ∀ (h : GB) u t, π (h • u) t = h • π u t)
    (hπl : ∀ u t, π u ((lA : GA) • t) = l • π u t) :
    P.boxCoeff N ∈ homogeneousMatrices Bg (fun p ↦ π (gr p.1) (grN p.2))
      (fun p ↦ π (gr p.1) (grN p.2)) l := by
  refine mem_homogeneousMatrices_iff.mpr fun p q ↦ ?_
  rw [boxCoeff_apply]
  refine finsum_induction (· ∈ _) (zero_mem _) (fun _ _ ↦ add_mem) fun k ↦ ?_
  rw [N.lift_iteratedCoeff, Matrix.sum_apply]
  refine Submodule.sum_mem _ fun r hr ↦ ?_
  obtain ⟨-, hr0, hrk⟩ := Finset.mem_filter.mp hr
  -- The coefficients along the path `r` are sums of homogeneous elements; by multilinearity it
  -- suffices to treat homogeneous coefficients.
  rw [← Matrix.entryLinearMap_apply R B p.1 q.1 (P.coeff k _), ← LinearMap.compMultilinearMap_apply]
  refine MultilinearMap.map_mem_of_mem_homogeneousMatrices
    ((Matrix.entryLinearMap R B p.1 q.1).compMultilinearMap (P.coeff k)) (F := fun _ ↦ N.coeff)
    (fun _ ↦ hN) r fun g a hg ha ↦ ?_
  refine Submodule.iSup_induction _ (motive := (· ∈ _))
    (mem_homogeneousMatrices_iff.mp (hP.coeff_mem ha) p.1 q.1) ?_ (zero_mem _) fun _ _ ↦ add_mem
  rintro ⟨h, hh⟩ b hb
  refine Submodule.mem_iSup_of_mem ⟨h, ?_⟩ hb
  -- The degrees along the path multiply to `l_A ^ k`, which `π` turns into `l ^ k`, and
  -- `δ¹_{k+1}` contributes `l ^ (1 - k)`.
  -- `Function.Semiconj f ga gb` is by definition `∀ x, f (ga x) = gb (f x)`, so `hπl u` is a
  -- semiconjugacy; the ascription names the two actions so that `iterate_right` applies.
  have hpow (j : ℕ) (u : U) (t : T) : π u ((lA : GA) ^ j • t) = l ^ j • π u t := by
    simpa only [smul_iterate] using
      (show Function.Semiconj (π u) ((lA : GA) • ·) (l • ·) from hπl u).iterate_right j t
  have hpath : (List.ofFn g).prod • grN (r (Fin.last k)) =
      (lA : GA) ^ k • grN (r 0) :=
    prod_ofFn_smul_eq_pow_smul (fun i ↦ Subgroup.mem_center_iff.mp lA.property (g i))
      (a := fun j ↦ grN (r j)) hg
  rw [← hπB, hh, hπB, hπA, ← hrk, hpath, hpow, smul_smul, ← hr0]
  congr 1
  group

end BoxTypeD

section Identity

variable {G : Type*} [Group G] {Ag : G → Submodule R A} {d : A →ₗ[R] A} {ι : S → A} [Fintype S]
  [CharP R 2] {X : Type*} [Fintype X] [DecidableEq X] {T : Type*} [MulAction G T]

/-- **The grading of `[I] ⊠ N`.** If the structure map of `N` has central degree `l` for a grading
`grN` of its generators, then so does the structure map of `[I] ⊠ N` for the grading
`(s, x) ↦ grN x`: the action map `G × T → T` is balanced and equivariant. -/
theorem boxCoeff_identity_mem_homogeneousMatrices (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1)
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h))
    (hι1 : ∀ s, ι s ∈ Ag 1) {N : TypeDStructure d ι X} {l : Subgroup.center G} {grN : X → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag grN grN l) :
    (identity ι hd hι hιι hsum).boxCoeff N ∈
      homogeneousMatrices Ag (fun p ↦ grN p.2) (fun p ↦ grN p.2) l := by
  simpa using (isGraded_identity hd hι hιι hsum hA hι1 l).boxCoeff_mem_homogeneousMatrices hN
    (π := fun u t ↦ u • t) (fun g u t ↦ by rw [op_smul_eq_mul, mul_smul])
    (fun h u t ↦ by rw [smul_eq_mul, mul_smul])
    fun u t ↦ by rw [smul_smul, smul_smul, Subgroup.mem_center_iff.mp l.property u]

end Identity

end TypeDAStructure

end TauCeti
