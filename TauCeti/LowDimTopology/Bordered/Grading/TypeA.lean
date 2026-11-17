/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Multilinear.Span
public import TauCeti.LowDimTopology.Bordered.Grading.Basic
public import TauCeti.LowDimTopology.Bordered.TypeA
import Mathlib.Tactic.Group

/-!
# Gradings of type `A` modules and of their box tensor products

The bordered algebras of Lipshitz, Ozsváth and Thurston are graded by a nonabelian group `G` with
a distinguished central element `λ`, and their modules are graded by `G`-sets. This file grades
the `A∞` right modules of `TauCeti.LowDimTopology.Bordered.TypeA`, the type `A` modules, and shows
that their box tensor products with graded type `D` structures are graded by the balanced product
of the two grading sets, with differential of degree `λ⁻¹`. It extends the gradings of
`TauCeti.LowDimTopology.Bordered.Grading.Basic`, which treat differential modules, to modules with
higher operations.

As there, the algebra `A` is graded by a family of submodules `Ag : G → Submodule R A`, a module
`M` by a family `Mg : S → Submodule R M` over a `G`-set `S` on which the right action is written
through inverses, `s · g = g⁻¹ • s`, and the central element `l` is the degree of the
differentials, `λ⁻¹` in the bordered algebras.

* **Graded `A∞` modules.** An `A∞` right module is graded
  (`TauCeti.UngradedAInfinityRightModule.IsGraded`) when its operation `m_{n+1}` has degree
  `λ^{n-1} = l^{1-n}`: for `m` of degree `s` and `aᵢ` of degree `gᵢ`,
  `m_{n+1}(m, a₁, …, aₙ)` has degree `s · l^{1-n} g₁ ⋯ gₙ`. So `m₁` has degree `l` and `m₂`
  is the graded right action. A differential module is graded in this sense exactly when its
  differential has degree `l` and its action is graded
  (`TauCeti.IsUngradedDGRightModule.isGraded_toUngradedAInfinityRightModule_iff`); in particular
  a graded differential algebra is a graded `A∞` module over itself
  (`TauCeti.IsUngradedDGAlgebra.isGraded_toUngradedAInfinityRightModule`).
* **Box tensor products.** The operations of the matrix module of a graded `A∞` module along
  matrices homogeneous of degree `l` raise the degree in the balanced product `S ×_G T` by `l`,
  whatever their arity: the `n` coefficients contribute `l^n` and the operation `l^{1-n}`
  (`TauCeti.UngradedAInfinityRightModule.IsGraded.matrixAct_mem_boxGradedPart`). Hence the box
  tensor differential `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))` has degree `l`
  (`TauCeti.TypeDStructure.typeABoxDifferential_mem_boxGradedPart`). No boundedness hypothesis
  is needed, since an infinite sum is `0` by the convention of
  `TauCeti.UngradedAInfinityRightModule.twistedDifferential`. A morphism of type `D` structures
  homogeneous of central degree `c` induces a map of box tensor products of degree `c`
  (`TauCeti.TypeDStructure.typeABoxMap_mem_boxGradedPart`). For morphisms of degrees `c` and
  `c'`, the construction `TauCeti.TypeDStructure.typeABoxCompHomotopy` has degree `l⁻¹ c c'`
  (`TauCeti.TypeDStructure.typeABoxCompHomotopy_mem_boxGradedPart`), one `l` below the degree of
  the composite. Over a ring of characteristic two, for homomorphisms and a bounded module or
  bounded type `D` structures, it is the homotopy comparing the composite of the induced maps with
  the map of the composite morphism, and this degree is the one its homotopy equation requires.

## Main definitions

* `TauCeti.UngradedAInfinityRightModule.IsGraded`: an `A∞` right module graded by a `G`-set,
  with `m_{n+1}` of degree `λ^{n-1}`.

## Main results

* `TauCeti.IsUngradedDGRightModule.isGraded_toUngradedAInfinityRightModule_iff`: the gradings of
  a differential module as an `A∞` module.
* `TauCeti.UngradedAInfinityRightModule.IsGraded.matrixAct_mem_boxGradedPart`: the operations of
  the matrix module along homogeneous matrices.
* `TauCeti.TypeDStructure.typeABoxDifferential_mem_boxGradedPart`: the box tensor differential
  of a graded `A∞` module with a graded type `D` structure is homogeneous of degree `l`.
* `TauCeti.TypeDStructure.typeABoxMap_mem_boxGradedPart` and
  `TauCeti.TypeDStructure.typeABoxCompHomotopy_mem_boxGradedPart`: the induced maps and the
  composition homotopies are homogeneous.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §2.5
  (gradings of `A∞` modules by `G`-sets, with `m_{n+1}` of degree `λ^{n-1}`, and of the box
  tensor product by the balanced product of the grading sets).
-/

public section

open MulOpposite

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {G : Type*} [Group G]
  {Ag : G → Submodule R A} {M : Type*} [AddCommGroup M] [Module R M] {S : Type*} [MulAction G S]
  {Mg : S → Submodule R M} {d : A →ₗ[R] A}

/-! ### Graded `A∞` modules -/

namespace UngradedAInfinityRightModule

/-- An `A∞` right module is **graded** by `Mg : S → Submodule R M` over the grading `Ag` of the
algebra, with central degree `l` of the differentials (`λ⁻¹` in the bordered algebras), when its
operation `m_{n+1}` has degree `λ^{n-1} = l^{1-n}`: for `m` of degree `s` and inputs `aᵢ` of
degrees `gᵢ`, `m_{n+1}(m, a₁, …, aₙ)` has degree `s · l^{1-n} g₁ ⋯ gₙ`, where the right action is
`s · g = g⁻¹ • s`. -/
def IsGraded (Mm : UngradedAInfinityRightModule d M) (Ag : G → Submodule R A)
    (Mg : S → Submodule R M) (l : G) : Prop :=
  ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
    m ∈ Mg s → Mm.act n a m ∈ Mg ((List.ofFn g).prod⁻¹ • l ^ ((n : ℤ) - 1) • s)

variable {Mm : UngradedAInfinityRightModule d M} {l : G}

/-- The definition of a graded `A∞` module, unfolded. -/
theorem isGraded_iff : Mm.IsGraded Ag Mg l ↔
    ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
      m ∈ Mg s → Mm.act n a m ∈ Mg ((List.ofFn g).prod⁻¹ • l ^ ((n : ℤ) - 1) • s) :=
  Iff.rfl

namespace IsGraded

/-- The operation `m_{n+1}` of a graded `A∞` module has degree `l^{1-n}`. -/
theorem act_mem (hMm : Mm.IsGraded Ag Mg l) {n : ℕ} {g : Fin n → G} {a : Fin n → A} {s : S}
    {m : M} (ha : ∀ i, a i ∈ Ag (g i)) (hm : m ∈ Mg s) :
    Mm.act n a m ∈ Mg ((List.ofFn g).prod⁻¹ • l ^ ((n : ℤ) - 1) • s) :=
  hMm n g a s m ha hm

/-- The differential `m₁` of a graded `A∞` module has degree `l`. -/
theorem act_zero_mem (hMm : Mm.IsGraded Ag Mg l) (a : Fin 0 → A) {s : S} {m : M}
    (hm : m ∈ Mg s) : Mm.act 0 a m ∈ Mg (l⁻¹ • s) := by
  simpa using hMm.act_mem (g := Fin.elim0) (fun i ↦ i.elim0) hm

/-- The operation `m₂` of a graded `A∞` module is a graded right action. -/
theorem act_one_mem (hMm : Mm.IsGraded Ag Mg l) {a : Fin 1 → A} {g : G} (ha : a 0 ∈ Ag g)
    {s : S} {m : M} (hm : m ∈ Mg s) : Mm.act 1 a m ∈ Mg (g⁻¹ • s) := by
  simpa using hMm.act_mem (n := 1) (g := fun _ ↦ g) (fun i ↦ by rwa [Subsingleton.elim i 0]) hm

end IsGraded

end UngradedAInfinityRightModule

namespace IsUngradedDGRightModule

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] {dM : M →ₗ[R] M} {l : G}

/-- **The gradings of a differential module as an `A∞` module.** A differential right module,
viewed as an `A∞` module, is graded with differentials of degree `l` exactly when its right action
is graded, `Mg s * Ag g ⊆ Mg (g⁻¹ • s)`, and its differential has degree `l`,
`dM (Mg s) ⊆ Mg (l⁻¹ • s)`: these are the hypotheses on differential modules in
`TauCeti.TypeDStructure.boxDifferential_mem_boxGradedPart`. -/
theorem isGraded_toUngradedAInfinityRightModule_iff [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) :
    hM.toUngradedAInfinityRightModule.IsGraded Ag Mg l ↔
      (∀ {s : S} {g : G} {m : M} {a : A}, m ∈ Mg s → a ∈ Ag g → op a • m ∈ Mg (g⁻¹ • s)) ∧
        ∀ {s : S} {m : M}, m ∈ Mg s → dM m ∈ Mg (l⁻¹ • s) := by
  refine ⟨fun h ↦ ⟨fun {s g m a} hm ha ↦ ?_, fun {s m} hm ↦ ?_⟩, fun ⟨hact, hdM⟩ ↦ ?_⟩
  · simpa using h.act_one_mem (a := fun _ ↦ a) ha hm
  · simpa using h.act_zero_mem Fin.elim0 hm
  · intro n g a s m ha hm
    match n with
    | 0 => simpa using hdM hm
    | 1 => simpa using hact hm (ha 0)
    | n + 2 =>
      rw [toUngradedAInfinityRightModule_act_add_two]
      exact zero_mem _

end IsUngradedDGRightModule

/-- **A graded differential algebra is a graded type `A` module over itself.** Let `A` be graded by
`Ag`, with `Ag g * Ag h ⊆ Ag (g * h)`, and let its differential have central degree `l`. Then `A`,
as an `A∞` right module over itself, is graded over the regular `G`-set by `Mg s = Ag s⁻¹`, with
differentials of degree `l`. -/
theorem IsUngradedDGAlgebra.isGraded_toUngradedAInfinityRightModule [CharP R 2]
    (hd : IsUngradedDGAlgebra d)
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h))
    {l : Subgroup.center G} (hdl : ∀ {g : G} {a : A}, a ∈ Ag g → d a ∈ Ag (l * g)) :
    hd.isUngradedDGRightModule.toUngradedAInfinityRightModule.IsGraded Ag (fun s : G ↦ Ag s⁻¹)
      l := by
  refine (IsUngradedDGRightModule.isGraded_toUngradedAInfinityRightModule_iff _).2
    ⟨fun {s g m a} hm ha ↦ ?_, fun {s m} hm ↦ ?_⟩
  · rw [op_smul_eq_mul, smul_eq_mul, mul_inv_rev, inv_inv]
    exact hA hm ha
  · rw [smul_eq_mul, mul_inv_rev, inv_inv, Subgroup.mem_center_iff.mp l.2 s⁻¹]
    exact hdl hm

/-! ### Gradings of box tensor products -/

namespace UngradedAInfinityRightModule

variable {T : Type*} [MulAction G T] {X : Type*}

variable [Fintype X] [DecidableEq X] {Mm : UngradedAInfinityRightModule d M}

/-- **The operations of the matrix module along homogeneous matrices.** Let `M` be a graded `A∞`
module with differentials of central degree `l`, and let `F₁, …, Fₙ` be matrices homogeneous of
degree `l`. Then `m_{n+1}(φ, F₁, …, Fₙ)` maps row vectors of degree `u ∈ S ×_G T` to row vectors
of degree `l • u`: the operation has degree `l^{1-n}` and the matrices contribute `l^n`. -/
theorem IsGraded.matrixAct_mem_boxGradedPart {l : Subgroup.center G}
    (hMm : Mm.IsGraded Ag Mg l) {gr : X → T} {n : ℕ} {F : Fin n → Matrix X X A}
    (hF : ∀ i, F i ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) : Mm.matrixAct X n F φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [mem_boxGradedPart_iff] at hφ ⊢
  intro z
  rw [matrixAct_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  split_ifs with hz
  swap
  · exact zero_mem _
  refine Submodule.iSup_induction _
    (motive := fun m ↦ Mm.act n (fun i ↦ F i (x i.castSucc) (x i.succ)) m ∈ _) (hφ (x 0)) ?_
    (by rw [map_zero]; exact zero_mem _) fun m m' hm hm' ↦ by rw [map_add]; exact add_mem hm hm'
  rintro ⟨s, hs⟩ m hm
  -- The entries along the path are sums of homogeneous elements; by multilinearity it suffices to
  -- treat homogeneous entries.
  let D (i : Fin n) : Set A :=
    ⋃ g : {g : G // g • gr (x i.succ) = (l : G) • gr (x i.castSucc)}, (Ag g : Set A)
  have hspan (i : Fin n) : F i (x i.castSucc) (x i.succ) ∈ Submodule.span R (D i) := by
    rw [← Submodule.iSup_eq_span]
    exact mem_homogeneousMatrices_iff.mp (hF i) _ _
  refine Submodule.span_le.mpr ?_
    (((LinearMap.applyₗ m).compMultilinearMap (Mm.act n)).map_mem_span_image_pi D hspan)
  rintro _ ⟨a, ha, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, D, Set.mem_iUnion, SetLike.mem_coe] at ha
  choose g hg using ha
  refine Submodule.mem_iSup_of_mem ⟨_, ?_⟩ (hMm.act_mem (g := fun i ↦ (g i : G)) hg hm)
  rw [← hz, BalancedProduct.mk_inv_prod_ofFn_zpow_smul l (fun i ↦ (g i : G)) (fun j ↦ gr (x j))
    (fun i ↦ (g i).2), hs]

/-- **The twisted differential of the matrix module along a homogeneous matrix.** For a graded
`A∞` module with differentials of central degree `l` and a matrix `C` homogeneous of degree `l`,
the twisted differential `∑ₙ m_{n+1}(·, C, …, C)` of the matrix module maps row vectors of degree
`u` to row vectors of degree `l • u`. No boundedness is needed: an infinite sum is `0` by the
convention of `TauCeti.UngradedAInfinityRightModule.twistedDifferential`. -/
theorem IsGraded.twistedDifferential_matrix_mem_boxGradedPart {l : Subgroup.center G}
    (hMm : Mm.IsGraded Ag Mg l) {gr : X → T} {C : Matrix X X A}
    (hC : C ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) :
    (Mm.matrix X).twistedDifferential C φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [twistedDifferential_def]
  refine finsum_induction (fun P : (X → M) →ₗ[R] X → M ↦ P φ ∈ boxGradedPart Mg gr (l • u))
    (zero_mem _) (fun P P' hP hP' ↦ add_mem hP hP') fun n ↦ ?_
  rw [matrix_act]
  exact hMm.matrixAct_mem_boxGradedPart (fun _ ↦ hC) hφ

end UngradedAInfinityRightModule

namespace TypeDStructure

variable {K : Type*} {ι : K → A} {T : Type*} [MulAction G T] {X X' X'' : Type*} [Fintype X]
  [DecidableEq X] [Fintype X'] [DecidableEq X'] {Mm : UngradedAInfinityRightModule d M}

/-- **The box tensor differential of a graded `A∞` module is homogeneous.** Let `M` be graded
with differentials of central degree `l`, and let the structure map of `N` have degree `l`. Then
the box tensor differential `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))` maps row vectors of
degree `u ∈ S ×_G T` to row vectors of degree `l • u`. -/
theorem typeABoxDifferential_mem_boxGradedPart {l : Subgroup.center G}
    (hMm : Mm.IsGraded Ag Mg l) {N : TypeDStructure d ι X} {gr : X → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) :
    N.typeABoxDifferential Mm φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [typeABoxDifferential_def]
  exact hMm.twistedDifferential_matrix_mem_boxGradedPart hN hφ

/-- **Induced maps of graded box tensor products.** Let `M` be a graded `A∞` module with
differentials of central degree `l`, let the structure maps of `N` and `N'` have degree `l`, and
let the morphism `F` from `N` to `N'` be homogeneous of central degree `c`. Then the induced map
`T_F` from `M ⊠ N` to `M ⊠ N'` maps row vectors of degree `u` to row vectors of degree `c • u`;
homomorphisms of degree `1` induce graded maps. -/
theorem typeABoxMap_mem_boxGradedPart {l : Subgroup.center G} (hMm : Mm.IsGraded Ag Mg l)
    {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'} {gr : X → T} {gr' : X' → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    (hN' : N'.coeff ∈ homogeneousMatrices Ag gr' gr' l) {c : Subgroup.center G}
    {F : Matrix X X' A} (hF : F ∈ homogeneousMatrices Ag gr gr' c) {u : BalancedProduct G S T}
    {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) :
    typeABoxMap N N' Mm F φ ∈ boxGradedPart Mg gr' (c • u) := by
  -- Translating the grading of `X'` by `k = l c⁻¹` makes `fromBlocks δ F 0 δ'` homogeneous of
  -- degree `l`, so the induced map is a component of a homogeneous box tensor differential.
  set k : Subgroup.center G := l * c⁻¹
  have hF' : F ∈ homogeneousMatrices Ag gr (fun y ↦ (k : G) • gr' y) l := by
    simpa [k] using (mem_homogeneousMatrices_smul_right_iff k.2).2 hF
  have hC : Matrix.fromBlocks N.coeff F 0 N'.coeff ∈
      homogeneousMatrices Ag (Sum.elim gr fun y ↦ (k : G) • gr' y)
        (Sum.elim gr fun y ↦ (k : G) • gr' y) l :=
    fromBlocks_mem_homogeneousMatrices_iff.2
      ⟨hN, hF', zero_mem _, (mem_homogeneousMatrices_smul_smul_iff k.2).2 hN'⟩
  rw [mem_boxGradedPart_iff]
  intro z
  rw [typeABoxMap_apply]
  have hk : k⁻¹ * l = c := by simp [k]
  rw [← hk, mul_smul]
  exact mem_iSup_mk_smul_iff.mp
    (hMm.twistedDifferential_matrix_mem_boxGradedPart hC
      (sumElim_zero_mem_boxGradedPart hφ) |> mem_boxGradedPart_iff.mp <| Sum.inr z)

/-- **The composition homotopies of graded box tensor products.** Let `M` be a graded `A∞` module
with differentials of central degree `l`, let the structure maps of `N`, `N'` and `N''` have
degree `l`, and let the morphisms `F` from `N` to `N'` and `G'` from `N'` to `N''` be homogeneous
of central degrees `c` and `c'`. Then `K = TauCeti.TypeDStructure.typeABoxCompHomotopy` maps row
vectors of degree `u` to row vectors of degree `(l⁻¹ * c * c') • u`, one `l` below the degree of
the composite. Over a ring of characteristic two, when `F` and `G'` are homomorphisms and `M`, or
`N`, `N'` and `N''`, are bounded, `K` satisfies `T_{G'} ∘ T_F + T_{F G'} = ∂'' ∘ K + K ∘ ∂`
(`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero` and
`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt`), so this is the degree
that equation requires. -/
theorem typeABoxCompHomotopy_mem_boxGradedPart [Fintype X''] [DecidableEq X'']
    {l : Subgroup.center G} (hMm : Mm.IsGraded Ag Mg l) {N : TypeDStructure d ι X}
    {N' : TypeDStructure d ι X'} {N'' : TypeDStructure d ι X''} {gr : X → T} {gr' : X' → T}
    {gr'' : X'' → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    (hN' : N'.coeff ∈ homogeneousMatrices Ag gr' gr' l)
    (hN'' : N''.coeff ∈ homogeneousMatrices Ag gr'' gr'' l) {c c' : Subgroup.center G}
    {F : Matrix X X' A} (hF : F ∈ homogeneousMatrices Ag gr gr' c) {G' : Matrix X' X'' A}
    (hG' : G' ∈ homogeneousMatrices Ag gr' gr'' c') {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) :
    typeABoxCompHomotopy N N' N'' Mm F G' φ ∈ boxGradedPart Mg gr'' ((l⁻¹ * c * c') • u) := by
  -- Translating the gradings of `X'` by `k = l c⁻¹` and of `X''` by `k' = l c'⁻¹ k` makes the
  -- block matrix with diagonal `δ, δ', δ''` and off-diagonal blocks `F`, `G'` homogeneous of
  -- degree `l`.
  set k : Subgroup.center G := l * c⁻¹
  set k' : Subgroup.center G := l * c'⁻¹ * k
  have hF' : F ∈ homogeneousMatrices Ag gr (fun y ↦ (k : G) • gr' y) l := by
    simpa [k] using (mem_homogeneousMatrices_smul_right_iff k.2).2 hF
  have hG'' : G' ∈ homogeneousMatrices Ag (fun y ↦ (k : G) • gr' y)
      (fun z ↦ (k' : G) • gr'' z) l := by
    have h := (mem_homogeneousMatrices_smul_right_iff (l * c'⁻¹ : Subgroup.center G).2
      (gr' := fun z ↦ (k : G) • gr'' z)).2 ((mem_homogeneousMatrices_smul_smul_iff k.2).2 hG')
    simpa [k', mul_smul] using h
  have hC : Matrix.fromBlocks N.coeff (Matrix.fromCols F 0) 0
      (Matrix.fromBlocks N'.coeff G' 0 N''.coeff) ∈
      homogeneousMatrices Ag
        (Sum.elim gr (Sum.elim (fun y ↦ (k : G) • gr' y) fun z ↦ (k' : G) • gr'' z))
        (Sum.elim gr (Sum.elim (fun y ↦ (k : G) • gr' y) fun z ↦ (k' : G) • gr'' z)) l :=
    fromBlocks_mem_homogeneousMatrices_iff.2 ⟨hN,
      fromCols_mem_homogeneousMatrices_iff.2 ⟨hF', zero_mem _⟩, zero_mem _,
      fromBlocks_mem_homogeneousMatrices_iff.2 ⟨(mem_homogeneousMatrices_smul_smul_iff k.2).2 hN',
        hG'', zero_mem _, (mem_homogeneousMatrices_smul_smul_iff k'.2).2 hN''⟩⟩
  rw [mem_boxGradedPart_iff]
  intro z
  rw [typeABoxCompHomotopy_apply]
  have hk : k'⁻¹ * l = l⁻¹ * c * c' := by
    have hcomm (a b : Subgroup.center G) : a * b = b * a :=
      Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
    rw [← hcomm c l⁻¹]
    simp only [k', k]
    group
  rw [← hk, mul_smul]
  exact mem_iSup_mk_smul_iff.mp
    (hMm.twistedDifferential_matrix_mem_boxGradedPart hC
      (sumElim_zero_mem_boxGradedPart hφ) |> mem_boxGradedPart_iff.mp <| Sum.inr (Sum.inr z))

end TypeDStructure

end TauCeti
