/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Matrix.Grading
public import TauCeti.LowDimTopology.Bordered.TypeD
public import TauCeti.Topology.Covering.BalancedProduct.Basic

/-!
# Gradings of type `D` structures and of box tensor products

The bordered algebras of Lipshitz, Ozsváth and Thurston are graded by a nonabelian group `G` with
a distinguished central element `λ`, and their modules are graded not by `G` itself but by
`G`-sets. This file sets up these gradings for the type `D` structures of
`TauCeti.LowDimTopology.Bordered.TypeD` and shows that the box tensor product of a graded
differential module with a graded type `D` structure is graded by the balanced product of the two
grading sets, with differential of degree `λ⁻¹`.

The algebra `A` is graded by a family of submodules `Ag : G → Submodule R A`. The results below
assume only the compatibilities they use: `Ag g * Ag h ⊆ Ag (g * h)`, and that the differential
`d` maps `Ag g` into `Ag (l * g)` for a central element `l` (in the bordered algebras
`l = λ⁻¹`, for instance `TauCeti.StrandsAlgebra.differential_mem_gradedPart`). That the parts
span `A` independently is never needed for these compatibilities.

* **Type `D` structures.** A type `D` structure `N` with generators `X` is graded by a left
  `G`-set `T` through a map `gr : X → T`; its structure map `δ¹ x = ∑ y, coeff x y ⊗ y` has
  degree `l` when each `coeff x y` is a sum of elements of degrees `g` with
  `g • gr y = l • gr x`, so that `gr (coeff x y ⊗ y) = l • gr x`. More generally a matrix `F` of
  morphisms is homogeneous of degree `c` when `F x y` is a sum of elements of degrees `g` with
  `g • gr' y = c • gr x` (`TauCeti.homogeneousMatrices`, in `TauCeti.Algebra.Matrix.Grading`).
  For central degrees these compose (`TauCeti.mul_mem_homogeneousMatrices`), the identity
  morphism has degree `1`, and the morphism differential raises the degree by `l`
  (`TauCeti.TypeDStructure.morphismDifferential_mem_homogeneousMatrices`).
* **Box tensor products.** A right `A`-module `M` is graded by a family `Mg : S → Submodule R M`
  over a right `G`-set `S`. Since `TauCeti.BalancedProduct` is built from left actions, the right
  action is written through inverses, `s · g = g⁻¹ • s`: the hypotheses read
  `Mg s * Ag g ⊆ Mg (g⁻¹ • s)` and `dM (Mg s) ⊆ Mg (l⁻¹ • s)`. A row vector `φ : X → M`, standing
  for `∑ x, φ x ⊗ x`, has degree `u` in the balanced product `S ×_G T` when each `φ x` is a sum of
  elements of the `Mg s` with `⟦s, gr x⟧ = u` (`TauCeti.boxGradedPart`). The balancing
  `⟦g⁻¹ • s, t⟧ = ⟦s, g • t⟧` is what makes `m * a ⊗ y` and `m ⊗ a y` have the same degree. A
  homogeneous matrix of central degree `c` maps the part of degree `u` into the part of degree
  `c • u` (`TauCeti.continuationMap_mem_boxGradedPart`), so homomorphisms of degree `1` induce
  graded maps, and the box tensor differential `∂ φ = dM φ + φ ⬝ δ` has degree `l`
  (`TauCeti.TypeDStructure.boxDifferential_mem_boxGradedPart`). For `M = A`, graded over the
  regular `G`-set by `Mg s = Ag s⁻¹`, this grades the induced differential module `A ⊠ N`
  (`TauCeti.TypeDStructure.boxDifferential_self_mem_boxGradedPart`).

## Main definitions

* `TauCeti.boxGradedPart Mg gr u`: the row vectors of degree `u` in the balanced product of the
  grading sets.

## Main results

* `TauCeti.TypeDStructure.idMorphism_mem_homogeneousMatrices`,
  `TauCeti.TypeDStructure.morphismDifferential_mem_homogeneousMatrices`: the graded morphism
  complex.
* `TauCeti.continuationMap_mem_boxGradedPart`: homogeneous morphisms act on box tensor products
  by the corresponding shift of the balanced product.
* `TauCeti.TypeDStructure.boxDifferential_mem_boxGradedPart`: the box tensor differential is
  homogeneous of degree `l`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §2.5
  (algebras graded by a group with a distinguished central element, modules and type `D`
  structures graded by `G`-sets, and the grading of the box tensor product by the balanced
  product of the grading sets).
-/

public section

open MulOpposite

namespace TauCeti

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {G : Type*} [Group G]
  {Ag : G → Submodule R A} {T : Type*} [MulAction G T] {X X' : Type*}

/-! ### The graded morphism complex -/

namespace TypeDStructure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {Ag : G → Submodule R A}
  {d : A →ₗ[R] A} {K : Type*} {ι : K → A} [Fintype X] [Fintype X']

/-- When the idempotents have degree `1`, the identity morphism of a type `D` structure is
homogeneous of degree `1` for any grading of its generators. -/
theorem idMorphism_mem_homogeneousMatrices [DecidableEq X] (N : TypeDStructure d ι X)
    (hι : ∀ k, ι k ∈ Ag 1) (gr : X → T) : N.idMorphism ∈ homogeneousMatrices Ag gr gr 1 := by
  refine mem_homogeneousMatrices_iff.mpr fun x y ↦ ?_
  rw [idMorphism_apply]
  split_ifs with h
  · subst h
    exact Submodule.mem_iSup_of_mem ⟨1, rfl⟩ (hι _)
  · exact zero_mem _

/-- **The graded morphism complex.** Let `d` and the structure maps of `N` and `N'` have the same
central degree `l` (in the bordered algebras, `λ⁻¹`). Then the differential of a morphism
homogeneous of central degree `c` is homogeneous of degree `l * c`. -/
theorem morphismDifferential_mem_homogeneousMatrices
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h)) {l c : G}
    (hd : ∀ {g : G} {a : A}, a ∈ Ag g → d a ∈ Ag (l * g)) (hl : l ∈ Subgroup.center G)
    (hc : c ∈ Subgroup.center G) {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'}
    {gr : X → T} {gr' : X' → T} (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    (hN' : N'.coeff ∈ homogeneousMatrices Ag gr' gr' l) {F : Matrix X X' A}
    (hF : F ∈ homogeneousMatrices Ag gr gr' c) :
    morphismDifferential N N' F ∈ homogeneousMatrices Ag gr gr' (l * c) := by
  have h₁ : F.map d ∈ homogeneousMatrices Ag gr gr' (l * c) :=
    map_mem_homogeneousMatrices (Ag := Ag) (d := d) (l := l) (gr := gr) (gr' := gr') hd hF
  have h₂ : F * N'.coeff ∈ homogeneousMatrices Ag gr gr' (l * c) := by
    have h := mul_mem_homogeneousMatrices hA hl hF hN'
    rwa [Subgroup.mem_center_iff.mp hl c] at h
  have h₃ : N.coeff * F ∈ homogeneousMatrices Ag gr gr' (l * c) :=
    mul_mem_homogeneousMatrices hA hc hN hF
  rw [morphismDifferential_apply]
  exact add_mem (add_mem h₁ h₂) h₃

end TypeDStructure

/-! ### Gradings of box tensor products -/

section BoxTensor

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {S : Type*} [MulAction G S] (Mg : S → Submodule R M)

/-- The row vectors `φ : X → M`, standing for `∑ x, φ x ⊗ x` in a box tensor product, **of degree
`u`** in the balanced product `S ×_G T` of the grading sets: each `φ x` is a sum of elements of
the `Mg s` with `⟦s, gr x⟧ = u`. -/
def boxGradedPart (gr : X → T) (u : BalancedProduct G S T) : Submodule R (X → M) where
  carrier := {φ | ∀ x, φ x ∈ ⨆ s : {s : S // BalancedProduct.mk G s (gr x) = u}, Mg s}
  add_mem' hφ hψ x := add_mem (hφ x) (hψ x)
  zero_mem' _ := zero_mem _
  smul_mem' r _ hφ x := Submodule.smul_mem _ r (hφ x)

variable {Mg}

@[simp]
theorem mem_boxGradedPart_iff {gr : X → T} {u : BalancedProduct G S T} {φ : X → M} :
    φ ∈ boxGradedPart Mg gr u ↔
      ∀ x, φ x ∈ ⨆ s : {s : S // BalancedProduct.mk G s (gr x) = u}, Mg s :=
  Iff.rfl

/-- A row vector supported on `X` has the degree of its `X`-part, whatever the grading of the
generators `Y` of the other summand. -/
theorem sumElim_zero_mem_boxGradedPart {Y : Type*} {gr : X → T} {grY : Y → T}
    {u : BalancedProduct G S T} {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) :
    Sum.elim φ 0 ∈ boxGradedPart Mg (Sum.elim gr grY) u := by
  rw [mem_boxGradedPart_iff] at hφ ⊢
  rintro (x | y)
  · exact hφ x
  · exact zero_mem _

/-- Reading the degree of an entry of a row vector at a generator whose grading was translated by a
central element `k`: it has degree `v` for the translated grading exactly when it has degree
`k⁻¹ • v` for the original one. -/
theorem mem_iSup_mk_smul_iff {k : Subgroup.center G} {t : T} {v : BalancedProduct G S T}
    {m : M} :
    m ∈ ⨆ s : {s : S // BalancedProduct.mk G s ((k : G) • t) = v}, Mg s ↔
      m ∈ ⨆ s : {s : S // BalancedProduct.mk G s t = k⁻¹ • v}, Mg s := by
  have h : (fun s : S ↦ BalancedProduct.mk G s ((k : G) • t) = v) =
      fun s ↦ BalancedProduct.mk G s t = k⁻¹ • v := by
    funext s
    rw [eq_inv_smul_iff, BalancedProduct.center_smul_mk]
  rw [h]

/-- **Homogeneous morphisms act on graded box tensor products.** If the right action of `A` on `M`
is graded, `Mg s * Ag g ⊆ Mg (g⁻¹ • s)`, a matrix homogeneous of central degree `c` maps row
vectors of degree `u` to row vectors of degree `c • u`. -/
theorem continuationMap_mem_boxGradedPart [Fintype X]
    (hM : ∀ {s : S} {g : G} {m : M} {a : A}, m ∈ Mg s → a ∈ Ag g → op a • m ∈ Mg (g⁻¹ • s))
    {gr : X → T} {gr' : X' → T} {c : Subgroup.center G} {F : Matrix X X' A}
    (hF : F ∈ homogeneousMatrices Ag gr gr' c) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) : continuationMap R M F φ ∈ boxGradedPart Mg gr' (c • u) := by
  intro x'
  rw [continuationMap_apply (R := R) (M := M) F]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  refine Submodule.iSup_induction _ (motive := fun m ↦ op (F x x') • m ∈ _) (hφ x) ?_
    (by rw [smul_zero]; exact zero_mem _) fun m m' hm hm' ↦ by rw [smul_add]; exact add_mem hm hm'
  rintro ⟨s, hs⟩ m hm
  refine Submodule.iSup_induction _ (motive := fun a ↦ op a • m ∈ _)
    (mem_homogeneousMatrices_iff.mp hF x x') ?_ (by rw [op_zero, zero_smul]; exact zero_mem _)
    fun a a' ha ha' ↦ by rw [op_add, add_smul]; exact add_mem ha ha'
  rintro ⟨g, hg⟩ a ha
  refine Submodule.mem_iSup_of_mem ⟨g⁻¹ • s, ?_⟩ (hM hm ha)
  rw [BalancedProduct.mk_smul_left, inv_inv, hg, ← hs, BalancedProduct.center_smul_mk]

end BoxTensor

section BoxDifferential

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {Ag : G → Submodule R A}
  {M : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {S : Type*} [MulAction G S] {Mg : S → Submodule R M}
  {d : A →ₗ[R] A} {K : Type*} {ι : K → A} [Fintype X]

/-- **The box tensor differential is homogeneous.** Let the structure map of `N` have central
degree `l`, and let the differential of `M` shift by `l` on the right,
`dM (Mg s) ⊆ Mg (l⁻¹ • s)`. Then the box tensor differential `∂ φ = dM φ + φ ⬝ δ` maps row
vectors of degree `u ∈ S ×_G T` to row vectors of degree `l • u`. -/
theorem TypeDStructure.boxDifferential_mem_boxGradedPart {N : TypeDStructure d ι X}
    (hM : ∀ {s : S} {g : G} {m : M} {a : A}, m ∈ Mg s → a ∈ Ag g → op a • m ∈ Mg (g⁻¹ • s))
    {dM : M →ₗ[R] M} {l : Subgroup.center G}
    (hdM : ∀ {s : S} {m : M}, m ∈ Mg s → dM m ∈ Mg ((l : G)⁻¹ • s)) {gr : X → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) : N.boxDifferential dM φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [boxDifferential_apply]
  refine add_mem (fun x ↦ ?_) (continuationMap_mem_boxGradedPart hM hN hφ)
  refine Submodule.iSup_induction _ (motive := fun m ↦ dM m ∈ _) (hφ x) ?_
    (by rw [map_zero]; exact zero_mem _) fun m m' hm hm' ↦ by rw [map_add]; exact add_mem hm hm'
  rintro ⟨s, hs⟩ m hm
  refine Submodule.mem_iSup_of_mem ⟨(l : G)⁻¹ • s, ?_⟩ (hdM hm)
  rw [BalancedProduct.mk_smul_left, inv_inv, ← hs, BalancedProduct.center_smul_mk]

/-- **The grading of the induced module `A ⊠ N`.** Grade `A`, as a right module over itself, by
the regular `G`-set through `Mg s = Ag s⁻¹`. If the structure map of `N` and the differential `d`
of `A` have central degree `l`, the differential of `A ⊠ N` maps row vectors of degree
`u ∈ G ×_G T` to row vectors of degree `l • u`. -/
theorem TypeDStructure.boxDifferential_self_mem_boxGradedPart {N : TypeDStructure d ι X}
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h))
    {l : Subgroup.center G} (hd : ∀ {g : G} {a : A}, a ∈ Ag g → d a ∈ Ag (l * g)) {gr : X → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G G T} {φ : X → A}
    (hφ : φ ∈ boxGradedPart (fun s : G ↦ Ag s⁻¹) gr u) :
    N.boxDifferential d φ ∈ boxGradedPart (fun s : G ↦ Ag s⁻¹) gr (l • u) := by
  refine boxDifferential_mem_boxGradedPart (fun {s g m a} hm ha ↦ ?_) (fun {s m} hm ↦ ?_) hN hφ
  · rw [op_smul_eq_mul, smul_eq_mul, mul_inv_rev, inv_inv]
    exact hA hm ha
  · rw [smul_eq_mul, mul_inv_rev, inv_inv, Subgroup.mem_center_iff.mp l.2 s⁻¹]
    exact hd hm

end BoxDifferential

end TauCeti
