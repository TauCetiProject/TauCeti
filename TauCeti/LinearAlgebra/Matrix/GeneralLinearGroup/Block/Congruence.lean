/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.upperTriangularCongruenceSubgroup`, `TauCeti.parahoricSubgroup`,
-- `TauCeti.unitriangularSubgroup`, and `Matrix.GeneralLinearGroup.map_surjective`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Congruence
-- `TauCeti.BlockTriangularGroup.diagBlocks` reads off the diagonal blocks.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Block

/-!
# Two-depth block congruence subgroups and their Levi quotients

Let `R` be a commutative ring, `lev : m → α` a ranking of the indices of square matrices by a
linear order, and `J`, `K` ideals of `R`. The **block congruence subgroup**
`P_lev(J, K) ⊆ GL_m(R)` consists of the invertible matrices that are block upper triangular for
`lev` modulo `K` and block upper unitriangular for `lev` modulo `J`: the entries below the diagonal
blocks lie in `K ⊓ J`, and the diagonal blocks are congruent to identity matrices modulo `J`.

Over the valuation ring `O` of a nonarchimedean local field with uniformizer `ϖ`, and for
`c ≥ b ≥ 0`, `c ≥ 1`, these are the standard deep levels at `p` of the theory of ordinary parts:

* for the identity ranking of a linearly ordered `m`, `P_id(ϖ^b, ϖ^c)` is the Iwahori level
  `Iw(b, c)` of matrices upper triangular modulo `ϖ^c` with diagonal congruent to `1` modulo
  `ϖ^b` (`TauCeti.blockCongruenceSubgroup_id`);
* for the two blocks of `m ⊕ n` ranked by `Sum.isRight`, so that `g = (A B; C D)`,
  `P(ϖ^b, ϖ^c)` consists of the `g` with `C ≡ 0 mod ϖ^c` and `A ≡ 1`, `D ≡ 1 mod ϖ^b`
  (`TauCeti.mem_blockCongruenceSubgroup_isRight_iff`); for `m = n` it is the Siegel level
  `P(b, c)` of `GL_{2n}(O)`, and `P(0, 1)`, with `J = ⊤` and `K = (ϖ)`, is the Siegel
  parahoric.

The membership condition only involves `K ⊓ J`, so one may always assume `K ≤ J`
(`TauCeti.blockCongruenceSubgroup_inf_right`). Then reducing modulo `J` and reading off the
diagonal blocks is a homomorphism from `P_lev(⊤, K)` to the Levi factor
`∏ₐ GL {i // lev i = a} (R ⧸ J)` whose kernel is `P_lev(J, K)`. When `J` lies in the Jacobson
radical, for instance when `R` is local and `J` is proper, invertible matrices lift modulo `J`, so
it is surjective, and

`P_lev(⊤, K) ⧸ P_lev(J, K) ≃* ∏ₐ GL {i // lev i = a} (R ⧸ J)`.

For the two blocks of `m ⊕ n` this reads `P(⊤, K) ⧸ P(J, K) ≃* GL_m(R ⧸ J) × GL_n(R ⧸ J)`, the
diamond quotient `P(0, c) ⧸ P(b, c) ≃ GL_n(O ⧸ ϖ^b) × GL_n(O ⧸ ϖ^b)` of the Siegel levels.

## Main declarations

* `TauCeti.blockCongruenceSubgroup lev J K`: the subgroup `P_lev(J, K)` of `GL_m(R)`.
* `TauCeti.mem_blockCongruenceSubgroup_iff`: membership through the entries.
* `TauCeti.blockCongruenceSubgroup_mono`: the subgroups grow with both ideals.
* `TauCeti.blockCongruenceSubgroup_top_left`: `P_lev(⊤, K)` is the parahoric congruence subgroup
  `TauCeti.parahoricSubgroup` of the dual ranking.
* `TauCeti.blockCongruenceSubgroup_id`: the identity ranking gives the Iwahori levels.
* `TauCeti.BlockCongruenceSubgroup.diagBlocks`: the diagonal blocks modulo `J`, with kernel
  `P_lev(J, K)` (`TauCeti.BlockCongruenceSubgroup.ker_diagBlocks`), surjective for `J` in the
  Jacobson radical (`TauCeti.BlockCongruenceSubgroup.diagBlocks_surjective`).
* `TauCeti.BlockCongruenceSubgroup.quotientEquiv`: `P_lev(⊤, K) ⧸ P_lev(J, K)` is the Levi factor
  modulo `J`.
* `TauCeti.mem_blockCongruenceSubgroup_isRight_iff`: membership for two blocks, in terms of the
  blocks `A`, `C` and `D`.
* `TauCeti.BlockCongruenceSubgroup.sumQuotientEquiv`: for two blocks,
  `P(⊤, K) ⧸ P(J, K) ≃* GL_m(R ⧸ J) × GL_n(R ⧸ J)`.

## References

* A. Caraiani and J. Newton, *On the modularity of elliptic curves over imaginary quadratic
  fields*, §2.1.13 (the Siegel levels `P(b, c)`).
* P. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023), §5.1
  (the Iwahori levels `Iw(b, c)`).
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

section Ranking

variable {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] (lev : m → α)

/-- The **block congruence subgroup** `P_lev(J, K)` of `GL_m(R)`: the invertible matrices that are
block upper triangular for the ranking `lev` modulo `K` and block upper unitriangular for `lev`
modulo `J`, that is, the intersection of the preimages of `blockTriangularGroup (R ⧸ K) lev` and of
`unitriangularSubgroup lev (R ⧸ J)` under reduction. -/
def blockCongruenceSubgroup (J K : Ideal R) : Subgroup (GL m R) :=
  (blockTriangularGroup (R ⧸ K) lev).comap (GeneralLinearGroup.map (Ideal.Quotient.mk K)) ⊓
    (unitriangularSubgroup lev (R ⧸ J)).comap (GeneralLinearGroup.map (Ideal.Quotient.mk J))

variable {lev} {J J' K K' : Ideal R}

omit [Fintype m] in
/-- An entry reduces modulo `J` to the corresponding entry of the identity matrix exactly when it
is congruent to it modulo `J`. -/
private theorem mk_eq_one_apply_iff {x : R} {i j : m} :
    Ideal.Quotient.mk J x = (1 : Matrix m m (R ⧸ J)) i j ↔ x - (1 : Matrix m m R) i j ∈ J := by
  have h1 : (1 : Matrix m m (R ⧸ J)) i j = Ideal.Quotient.mk J ((1 : Matrix m m R) i j) := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, Ideal.Quotient.eq]

/-- Membership in the block congruence subgroup `P_lev(J, K)`: the entries below the diagonal
blocks lie in `K ⊓ J`, and the diagonal blocks are congruent to identity matrices modulo `J`. -/
@[simp]
theorem mem_blockCongruenceSubgroup_iff {g : GL m R} :
    g ∈ blockCongruenceSubgroup lev J K ↔
      (∀ ⦃i j⦄, lev j < lev i → (g : Matrix m m R) i j ∈ K ⊓ J) ∧
        ∀ ⦃i j⦄, lev i = lev j → (g : Matrix m m R) i j - (1 : Matrix m m R) i j ∈ J := by
  simp only [blockCongruenceSubgroup, Subgroup.mem_inf, Subgroup.mem_comap,
    mem_blockTriangularGroup_iff, mem_unitriangularSubgroup, blockUnitriangular_iff,
    BlockTriangular, GeneralLinearGroup.map_apply, Ideal.Quotient.eq_zero_iff_mem,
    mk_eq_one_apply_iff, Submodule.mem_inf]
  grind

/-- Membership in the block congruence subgroup `P_lev(J, K)` for `K ≤ J`: the entries below the
diagonal blocks lie in `K`, and the diagonal blocks are congruent to identity matrices modulo
`J`. -/
theorem mem_blockCongruenceSubgroup_iff_of_le (hKJ : K ≤ J) {g : GL m R} :
    g ∈ blockCongruenceSubgroup lev J K ↔
      (∀ ⦃i j⦄, lev j < lev i → (g : Matrix m m R) i j ∈ K) ∧
        ∀ ⦃i j⦄, lev i = lev j → (g : Matrix m m R) i j - (1 : Matrix m m R) i j ∈ J := by
  rw [mem_blockCongruenceSubgroup_iff, inf_eq_left.mpr hKJ]

/-- The block congruence subgroup only depends on `K` through `K ⊓ J`. -/
@[simp]
theorem blockCongruenceSubgroup_inf_right :
    blockCongruenceSubgroup lev J (K ⊓ J) = blockCongruenceSubgroup lev J K := by
  ext g
  simp only [mem_blockCongruenceSubgroup_iff, inf_assoc, inf_idem]

/-- The block congruence subgroup grows with both ideals. -/
theorem blockCongruenceSubgroup_mono (hJ : J ≤ J') (hK : K ≤ K') :
    blockCongruenceSubgroup lev J K ≤ blockCongruenceSubgroup lev J' K' := fun _ hg ↦ by
  rw [mem_blockCongruenceSubgroup_iff] at hg ⊢
  exact ⟨fun _ _ h ↦ inf_le_inf hK hJ (hg.1 h), fun _ _ h ↦ hJ (hg.2 h)⟩

/-- Modulo the unit ideal for the diagonal blocks, the block congruence subgroup is the parahoric
congruence subgroup of the dual ranking: the invertible matrices that are block upper triangular
for `lev` modulo `K`. -/
theorem blockCongruenceSubgroup_top_left :
    blockCongruenceSubgroup lev ⊤ K = parahoricSubgroup (OrderDual.toDual ∘ lev) K := by
  ext g
  simp

/-- Modulo the unit ideal, every invertible matrix lies in the block congruence subgroup. -/
@[simp]
theorem blockCongruenceSubgroup_top_top : blockCongruenceSubgroup lev (⊤ : Ideal R) ⊤ = ⊤ := by
  ext g
  simp

/-! ### The diagonal blocks modulo `J` -/

namespace BlockCongruenceSubgroup

/-- For `K ≤ J`, reduction modulo `J` maps `P_lev(⊤, K)` into the block triangular matrices over
`R ⧸ J`. -/
private theorem map_mem_blockTriangularGroup (hKJ : K ≤ J)
    (g : blockCongruenceSubgroup lev ⊤ K) :
    GeneralLinearGroup.map (Ideal.Quotient.mk J) (g : GL m R) ∈
      blockTriangularGroup (R ⧸ J) lev := by
  have hg := (mem_blockCongruenceSubgroup_iff_of_le le_top).mp g.property
  exact mem_blockTriangularGroup_iff.mpr fun i j h ↦ by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hKJ (hg.1 h)

variable (lev) in
/-- The **diagonal blocks modulo `J`** of an element of `P_lev(⊤, K)`, for `K ≤ J`: the projection
onto the Levi factor `∏ₐ GL {i // lev i = a} (R ⧸ J)`, through reduction modulo `J`. -/
def diagBlocks (hKJ : K ≤ J) :
    blockCongruenceSubgroup lev ⊤ K →* ((a : α) → GL {i // lev i = a} (R ⧸ J)) :=
  (BlockTriangularGroup.diagBlocks (R ⧸ J) lev).comp
    (((GeneralLinearGroup.map (Ideal.Quotient.mk J)).domRestrict
      (blockCongruenceSubgroup lev ⊤ K)).codRestrict _ fun g ↦ by
        simpa only [MonoidHom.domRestrict_apply] using map_mem_blockTriangularGroup hKJ g)

/-- The diagonal block `a` modulo `J` is the diagonal block `a`, reduced modulo `J`. -/
@[simp]
theorem coe_diagBlocks_apply (hKJ : K ≤ J) (g : blockCongruenceSubgroup lev ⊤ K) (a : α) :
    (diagBlocks lev hKJ g a : Matrix {i // lev i = a} {i // lev i = a} (R ⧸ J)) =
      (((g : GL m R) : Matrix m m R).toSquareBlock lev a).map (Ideal.Quotient.mk J) := by
  rw [diagBlocks, MonoidHom.comp_apply, BlockTriangularGroup.diagBlocks_apply,
    BlockTriangularGroup.coe_diagBlock]
  ext i j
  simp [toSquareBlock_def]

/-- The kernel of the diagonal blocks modulo `J` is `P_lev(J, K)`. -/
theorem ker_diagBlocks (hKJ : K ≤ J) :
    (diagBlocks lev hKJ).ker =
      (blockCongruenceSubgroup lev J K).subgroupOf (blockCongruenceSubgroup lev ⊤ K) := by
  ext g
  have hg := (mem_blockCongruenceSubgroup_iff_of_le le_top).mp g.property
  rw [diagBlocks, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    BlockTriangularGroup.mem_ker_diagBlocks_iff, Subgroup.mem_subgroupOf,
    mem_blockCongruenceSubgroup_iff_of_le hKJ]
  simp only [MonoidHom.codRestrict_apply, MonoidHom.domRestrict_apply,
    GeneralLinearGroup.map_apply, mk_eq_one_apply_iff]
  exact ⟨fun h ↦ ⟨hg.1, h⟩, fun h ↦ h.2⟩

/-- For `K ≤ J`, the block congruence subgroup `P_lev(J, K)` is normal in `P_lev(⊤, K)`. -/
theorem normal_subgroupOf (hKJ : K ≤ J) :
    ((blockCongruenceSubgroup lev J K).subgroupOf (blockCongruenceSubgroup lev ⊤ K)).Normal :=
  ker_diagBlocks (lev := lev) hKJ ▸ (diagBlocks lev hKJ).normal_ker

/-- If `J` lies in the Jacobson radical, the diagonal blocks modulo `J` are arbitrary: every
element of the Levi factor over `R ⧸ J` is attained by a block diagonal matrix over `R`. -/
theorem diagBlocks_surjective [Finite α] (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R) :
    Function.Surjective (diagBlocks lev hKJ) := by
  have := Fintype.ofFinite α
  have := isLocalHom_of_le_jacobson hJ
  intro h
  choose l hl using fun a ↦
    GeneralLinearGroup.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (h a)
  set x := BlockTriangularGroup.blockDiagonalHom R lev l
  have hx : (x : GL m R) ∈ blockCongruenceSubgroup lev ⊤ K :=
    (mem_blockCongruenceSubgroup_iff_of_le le_top).mpr
      ⟨fun i j hij ↦ by
        rw [mem_blockTriangularGroup_iff.mp x.property hij]
        exact zero_mem K,
        fun _ _ _ ↦ Submodule.mem_top⟩
  refine ⟨⟨x, hx⟩, funext fun a ↦ Units.ext ?_⟩
  have hxa := congrFun (BlockTriangularGroup.diagBlocks_blockDiagonalHom l) a
  rw [BlockTriangularGroup.diagBlocks_apply] at hxa
  rw [coe_diagBlocks_apply, ← hl a, ← hxa]
  ext i j
  simp [toSquareBlock_def, x]

/-- If `K ≤ J` and `J` lies in the Jacobson radical, the diagonal blocks modulo `J` identify the
quotient of `P_lev(⊤, K)` by `P_lev(J, K)` with the Levi factor `∏ₐ GL {i // lev i = a} (R ⧸ J)`.
The normality of `P_lev(J, K)` is `TauCeti.BlockCongruenceSubgroup.normal_subgroupOf`. -/
noncomputable def quotientEquiv [Finite α] (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R)
    [((blockCongruenceSubgroup lev J K).subgroupOf (blockCongruenceSubgroup lev ⊤ K)).Normal] :
    blockCongruenceSubgroup lev ⊤ K ⧸
        (blockCongruenceSubgroup lev J K).subgroupOf (blockCongruenceSubgroup lev ⊤ K) ≃*
      ((a : α) → GL {i // lev i = a} (R ⧸ J)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_diagBlocks hKJ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (diagBlocks_surjective hKJ hJ))

/-- The identification of the quotient sends a class to the diagonal blocks modulo `J` of a
representative. -/
@[simp]
theorem quotientEquiv_mk [Finite α] (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R)
    [((blockCongruenceSubgroup lev J K).subgroupOf (blockCongruenceSubgroup lev ⊤ K)).Normal]
    (g : blockCongruenceSubgroup lev ⊤ K) :
    quotientEquiv hKJ hJ (g : blockCongruenceSubgroup lev ⊤ K ⧸
        (blockCongruenceSubgroup lev J K).subgroupOf (blockCongruenceSubgroup lev ⊤ K)) =
      diagBlocks lev hKJ g :=
  (rfl)

end BlockCongruenceSubgroup

open BlockCongruenceSubgroup in
/-- If `K ≤ J` and `J` lies in the Jacobson radical, the index of `P_lev(J, K)` in `P_lev(⊤, K)` is
the order of the Levi factor `∏ₐ GL {i // lev i = a} (R ⧸ J)`. -/
theorem relIndex_blockCongruenceSubgroup [Finite α] (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R) :
    (blockCongruenceSubgroup lev J K).relIndex (blockCongruenceSubgroup lev ⊤ K) =
      Nat.card ((a : α) → GL {i // lev i = a} (R ⧸ J)) := by
  rw [Subgroup.relIndex, ← ker_diagBlocks hKJ, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (diagBlocks_surjective hKJ hJ), Subgroup.card_top]

end Ranking

/-! ### The Iwahori levels -/

section Iwahori

variable {m : Type*} [Fintype m] [LinearOrder m] {J K : Ideal R}

/-- For the identity ranking of a linearly ordered index type, the block congruence subgroup
`P_id(J, K)` is the Iwahori level: the invertible matrices that are upper triangular modulo `K`
and upper unitriangular modulo `J`. -/
theorem blockCongruenceSubgroup_id :
    blockCongruenceSubgroup (id : m → m) J K =
      upperTriangularCongruenceSubgroup m K ⊓ upperUnitriangularCongruenceSubgroup m J := by
  ext g
  simp only [mem_blockCongruenceSubgroup_iff, id, Submodule.mem_inf, Subgroup.mem_inf,
    mem_upperTriangularCongruenceSubgroup_iff, mem_upperUnitriangularCongruenceSubgroup_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i j h ↦ (h₁ h).1, fun i j h ↦ (h₁ h).2, fun i ↦ by simpa using h₂ (rfl : i = i)⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun i j h ↦ ⟨h₁ h, h₂ h⟩, fun i j h ↦ ?_⟩
    subst h
    simpa using h₃ i

end Iwahori

/-! ### Two blocks -/

section Sum

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {J K : Ideal R}

/-- Membership in the block congruence subgroup of `m ⊕ n` ranked by `Sum.isRight`, for `K ≤ J`:
writing `g = (A B; C D)` in blocks, `C ≡ 0` modulo `K`, and `A ≡ 1`, `D ≡ 1` modulo `J`. -/
theorem mem_blockCongruenceSubgroup_isRight_iff (hKJ : K ≤ J) {g : GL (m ⊕ n) R} :
    g ∈ blockCongruenceSubgroup Sum.isRight J K ↔
      (∀ i j, (g : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₁ i j ∈ K) ∧
        (∀ i j, ((g : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₁₁ - 1) i j ∈ J) ∧
          ∀ i j, ((g : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₂ - 1) i j ∈ J := by
  rw [mem_blockCongruenceSubgroup_iff_of_le hKJ]
  simp [Sum.forall, toBlocks₁₁, toBlocks₂₁, toBlocks₂₂, Matrix.one_apply]

variable (m n) in
/-- The Levi factor of the ranking `Sum.isRight` of `m ⊕ n` is `GL_m × GL_n`: the diagonal block of
`false` is indexed by the left summand and that of `true` by the right summand. -/
def sumIsRightLeviEquiv (S : Type*) [CommRing S] :
    ((a : Bool) → GL {i : m ⊕ n // i.isRight = a} S) ≃* GL m S × GL n S where
  toFun h :=
    (GeneralLinearGroup.reindex S
        ((Equiv.subtypeEquivRight fun _ ↦ Sum.isRight_eq_false).trans Equiv.sumIsLeft) (h false),
      GeneralLinearGroup.reindex S Equiv.sumIsRight (h true))
  invFun p
    | false => (GeneralLinearGroup.reindex S
        ((Equiv.subtypeEquivRight fun _ ↦ Sum.isRight_eq_false).trans Equiv.sumIsLeft)).symm p.1
    | true => (GeneralLinearGroup.reindex S Equiv.sumIsRight).symm p.2
  left_inv _ := funext fun
    | false => MulEquiv.symm_apply_apply _ _
    | true => MulEquiv.symm_apply_apply _ _
  right_inv _ := Prod.ext (MulEquiv.apply_symm_apply _ _) (MulEquiv.apply_symm_apply _ _)
  map_mul' _ _ := Prod.ext (map_mul _ _ _) (map_mul _ _ _)

/-- The first component of `sumIsRightLeviEquiv` is the block of `false`, indexed by `m`. -/
@[simp]
theorem coe_sumIsRightLeviEquiv_apply_fst {S : Type*} [CommRing S]
    (h : (a : Bool) → GL {i : m ⊕ n // i.isRight = a} S) (i j : m) :
    ((sumIsRightLeviEquiv m n S h).1 : Matrix m m S) i j =
      ((h false : GL {i : m ⊕ n // i.isRight = false} S) :
        Matrix {i : m ⊕ n // i.isRight = false} {i : m ⊕ n // i.isRight = false} S)
        ⟨Sum.inl i, rfl⟩ ⟨Sum.inl j, rfl⟩ :=
  (rfl)

/-- The second component of `sumIsRightLeviEquiv` is the block of `true`, indexed by `n`. -/
@[simp]
theorem coe_sumIsRightLeviEquiv_apply_snd {S : Type*} [CommRing S]
    (h : (a : Bool) → GL {i : m ⊕ n // i.isRight = a} S) (i j : n) :
    ((sumIsRightLeviEquiv m n S h).2 : Matrix n n S) i j =
      ((h true : GL {i : m ⊕ n // i.isRight = true} S) :
        Matrix {i : m ⊕ n // i.isRight = true} {i : m ⊕ n // i.isRight = true} S)
        ⟨Sum.inr i, rfl⟩ ⟨Sum.inr j, rfl⟩ :=
  (rfl)

namespace BlockCongruenceSubgroup

/-- The **diagonal blocks modulo `J`** for the two blocks of `m ⊕ n`, for `K ≤ J`: the
homomorphism `P(⊤, K) →* GL_m(R ⧸ J) × GL_n(R ⧸ J)` sending `(A B; C D)` to `A` and `D` modulo
`J`. -/
def sumDiagBlocks (hKJ : K ≤ J) :
    blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) ⊤ K →* GL m (R ⧸ J) × GL n (R ⧸ J) :=
  (sumIsRightLeviEquiv m n (R ⧸ J) : _ →* GL m (R ⧸ J) × GL n (R ⧸ J)).comp
    (diagBlocks Sum.isRight hKJ)

/-- The first component of `sumDiagBlocks` is the upper-left block, reduced modulo `J`. -/
@[simp]
theorem coe_sumDiagBlocks_fst (hKJ : K ≤ J)
    (g : blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) ⊤ K) :
    ((sumDiagBlocks hKJ g).1 : Matrix m m (R ⧸ J)) =
      ((g : GL (m ⊕ n) R) : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₁₁.map (Ideal.Quotient.mk J) := by
  ext i j
  simp [sumDiagBlocks, toSquareBlock_def, toBlocks₁₁]

/-- The second component of `sumDiagBlocks` is the lower-right block, reduced modulo `J`. -/
@[simp]
theorem coe_sumDiagBlocks_snd (hKJ : K ≤ J)
    (g : blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) ⊤ K) :
    ((sumDiagBlocks hKJ g).2 : Matrix n n (R ⧸ J)) =
      ((g : GL (m ⊕ n) R) : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₂.map (Ideal.Quotient.mk J) := by
  ext i j
  simp [sumDiagBlocks, toSquareBlock_def, toBlocks₂₂]

/-- The kernel of `sumDiagBlocks` is `P(J, K)`. -/
theorem ker_sumDiagBlocks (hKJ : K ≤ J) :
    (sumDiagBlocks (m := m) (n := n) hKJ).ker =
      (blockCongruenceSubgroup Sum.isRight J K).subgroupOf
        (blockCongruenceSubgroup Sum.isRight ⊤ K) := by
  rw [sumDiagBlocks, MonoidHom.ker_mulEquiv_comp, ker_diagBlocks]

/-- If `J` lies in the Jacobson radical, `sumDiagBlocks` is surjective. -/
theorem sumDiagBlocks_surjective (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R) :
    Function.Surjective (sumDiagBlocks (m := m) (n := n) hKJ) :=
  (sumIsRightLeviEquiv m n (R ⧸ J)).surjective.comp (diagBlocks_surjective hKJ hJ)

/-- If `K ≤ J` and `J` lies in the Jacobson radical, the upper-left and lower-right blocks modulo
`J` identify the quotient of `P(⊤, K)` by `P(J, K)` with `GL_m(R ⧸ J) × GL_n(R ⧸ J)`. For `m = n`,
`J = 𝔭 ^ b` and `K = 𝔭 ^ c` this is the diamond quotient `P(0, c) ⧸ P(b, c)` of the Siegel
levels. -/
noncomputable def sumQuotientEquiv (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R)
    [((blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) J K).subgroupOf
      (blockCongruenceSubgroup Sum.isRight ⊤ K)).Normal] :
    blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) ⊤ K ⧸
        (blockCongruenceSubgroup Sum.isRight J K).subgroupOf
          (blockCongruenceSubgroup Sum.isRight ⊤ K) ≃*
      GL m (R ⧸ J) × GL n (R ⧸ J) :=
  (quotientEquiv hKJ hJ).trans (sumIsRightLeviEquiv m n (R ⧸ J))

/-- The identification of the quotient sends a class to the upper-left and lower-right blocks
modulo `J` of a representative. -/
@[simp]
theorem sumQuotientEquiv_mk (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R)
    [((blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) J K).subgroupOf
      (blockCongruenceSubgroup Sum.isRight ⊤ K)).Normal]
    (g : blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) ⊤ K) :
    sumQuotientEquiv hKJ hJ (g : blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) ⊤ K ⧸
        (blockCongruenceSubgroup Sum.isRight J K).subgroupOf
          (blockCongruenceSubgroup Sum.isRight ⊤ K)) =
      sumDiagBlocks hKJ g :=
  (rfl)

end BlockCongruenceSubgroup

open BlockCongruenceSubgroup in
/-- If `K ≤ J` and `J` lies in the Jacobson radical, the index of `P(J, K)` in `P(⊤, K)` for the two
blocks of `m ⊕ n` is `#GL_m(R ⧸ J) · #GL_n(R ⧸ J)`. -/
theorem relIndex_blockCongruenceSubgroup_isRight (hKJ : K ≤ J) (hJ : J ≤ Ring.jacobson R) :
    (blockCongruenceSubgroup (Sum.isRight : m ⊕ n → Bool) J K).relIndex
        (blockCongruenceSubgroup Sum.isRight ⊤ K) =
      Nat.card (GL m (R ⧸ J)) * Nat.card (GL n (R ⧸ J)) := by
  rw [Subgroup.relIndex, ← ker_sumDiagBlocks hKJ, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (sumDiagBlocks_surjective hKJ hJ), Subgroup.card_top,
    Nat.card_prod]

end Sum

end TauCeti
