/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.CategoryTheory.Graded.Multilinear.Basic
public import TauCeti.CategoryTheory.Graded.TotalHom

/-!
# A-infinity categories

An uncurved nonunital **`A∞` category** on a graded linear quiver `C` over a commutative ring `R`
has, for every composable string `X₀, …, Xₙ` of objects with `n ≥ 1`, an operation

`mₙ : Hom(Xₙ₋₁, Xₙ) ⊗ ⋯ ⊗ Hom(X₀, X₁) ⟶ Hom(X₀, Xₙ)`

of degree `2 - n`, subject to the Stasheff identities on every composable string.

The structure is stored as an `A∞` algebra on the total module of morphisms
`⨁ (X, Y), Hom(X, Y)` with its degreewise grading, whose operations are path-compatible
(`TauCeti.GradedLinearQuiver.IsPathCompatible`): they send a composable string to a morphism
between its endpoints, and every other string to zero.  A path-compatible operation is determined
by its values on composable strings, so this is exactly the data of the operations `mₙ` above.
The stored law is therefore the square-zero law `b ∘ b = 0` of the suspended bar coderivation of
the total module, as for `TauCeti.AInfinityAlgebra`.  On a word of morphisms which is not
composable every term of the Stasheff identities vanishes, so these identities on the total module
are exactly the Stasheff identities on composable strings.  Constructions on `A∞` algebras, such as
the bar differential and the unsuspended Stasheff identities, apply to the total algebra
directly.

The operation `mₙ` on a single composable string is
`TauCeti.AInfinityCategory.pathOperation`, a `TauCeti.GradedLinearQuiver.PathOperation` of
degree `2 - n`, with inputs in Keller's order `(aₙ, …, a₁)`.  The arity-one and arity-two
operations are the differential `TauCeti.AInfinityCategory.homDifferential` of each hom module
and the composition `TauCeti.AInfinityCategory.comp`, with `m₂(g, f) = g ∘ f`.  The
differential squares to zero and satisfies the Leibniz rule
`d (g ∘ f) = d g ∘ f + (-1)^{|g|} g ∘ d f`.

## Main definitions

* `TauCeti.AInfinityCategory`: an uncurved nonunital `A∞` category on a graded linear quiver.
* `TauCeti.AInfinityCategory.pathOperation`: the operation `mₙ` on a composable string.
* `TauCeti.AInfinityCategory.homDifferential`: the differential `m₁` of a hom module.
* `TauCeti.AInfinityCategory.comp`: the composition `m₂`.

## Main results

* `TauCeti.AInfinityCategory.homInclusion_pathOperation`: the operation on a composable string
  is the total operation on the included morphisms.
* `TauCeti.AInfinityCategory.ext_pathOperation`: an `A∞` category is determined by its
  operations on composable strings.
* `TauCeti.AInfinityCategory.homDifferential_homDifferential`: the differential squares to zero.
* `TauCeti.AInfinityCategory.homDifferential_comp`: the Leibniz rule.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
-/

public section

open scoped BigOperators

namespace TauCeti

universe u v w

open GradedLinearQuiver

/-- An uncurved nonunital **`A∞` category** on a graded linear quiver `C`: an `A∞` algebra on
the total module of morphisms `⨁ (X, Y), Hom(X, Y)`, graded degreewise, whose operations are
path-compatible.  Its operation `mₙ` on a composable string `X₀, …, Xₙ` is
`TauCeti.AInfinityCategory.pathOperation`. -/
structure AInfinityCategory (R : Type w) [CommRing R] (C : Type u)
    [GradedLinearQuiver.{u, v, w} R C] extends AInfinityAlgebra R (TotalHom R C) where
  /-- The grading of the total algebra is the degreewise grading of the morphisms. -/
  grading_eq : grading = totalGrading R C
  /-- Every operation of positive arity sends composable strings to morphisms between their
  endpoints, and other strings to zero.  The nullary operation vanishes, so it is path-compatible
  automatically (`TauCeti.AInfinityCategory.isPathCompatible_m`). -/
  isPathCompatible_m_of_pos (n : ℕ) (hn : 0 < n) : IsPathCompatible (m n)

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- `A∞` categories on a graded linear quiver are determined by their operations. -/
theorem ext {𝒞 𝒞' : AInfinityCategory R C} (h : 𝒞.m = 𝒞'.m) : 𝒞 = 𝒞' := by
  obtain ⟨𝒜, hG, hm⟩ := 𝒞
  obtain ⟨𝒜', hG', hm'⟩ := 𝒞'
  obtain rfl : 𝒜 = 𝒜' := AInfinityAlgebra.ext (hG.trans hG'.symm) h
  rfl

variable (𝒞 : AInfinityCategory R C)

/-- Every operation of an `A∞` category sends composable strings to morphisms between their
endpoints, and other strings to zero. -/
theorem isPathCompatible_m (n : ℕ) : IsPathCompatible (𝒞.m n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [𝒞.m_zero]
    exact ⟨fun _ _ ↦ zero_mem _, fun _ _ _ _ _ _ _ ↦ rfl⟩
  · exact 𝒞.isPathCompatible_m_of_pos n hn

/-- The operation `mₙ` sends inputs of degrees `dᵢ` to an element of degree `∑ dᵢ + 2 - n`. -/
theorem m_mem_totalGrading_piece {n : ℕ} (d : Fin n → ℤ) (x : Fin n → TotalHom R C)
    (hx : ∀ i, x i ∈ (totalGrading R C).piece (d i)) :
    𝒞.m n x ∈ (totalGrading R C).piece ((∑ i, d i) + (2 - n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← 𝒞.grading_eq] at hx ⊢
    exact (𝒞.m_degree n hn).map_mem d x hx

/-- The operation `mₙ` on the composable string `X₀, …, Xₙ`: a multilinear map of degree `2 - n`
from the homogeneous morphisms `Xₙ₋₁ ⟶ Xₙ, …, X₀ ⟶ X₁` to the morphisms `X₀ ⟶ Xₙ`. -/
noncomputable def pathOperation {n : ℕ} (X : Fin (n + 1) → C) : PathOperation R X (2 - n) :=
  fun d ↦ MultilinearMap.codRestrict
    ((homProjection (X 0) (X (Fin.last n))).compMultilinearMap
      ((𝒞.m n).compLinearMap fun i ↦ homInclusion _ _ ∘ₗ
        ((grading (R := R) (X i.rev.castSucc) (X i.rev.succ)).piece (d i)).subtype))
    _ fun y ↦ homProjection_mem_piece
      (𝒞.m_mem_totalGrading_piece d _ fun i ↦
        (homInclusion_mem_totalGrading_piece_iff _ _).2 (y i).property) _ _

/-- The operation on a composable string is the component, between the endpoints of the string, of
the total operation on the included morphisms. -/
theorem coe_pathOperation_apply {n : ℕ} (X : Fin (n + 1) → C) (d : Fin n → ℤ)
    (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    (𝒞.pathOperation X d x : homModule (R := R) (X 0) (X (Fin.last n))) =
      homProjection (X 0) (X (Fin.last n))
        (𝒞.m n fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (x i).1) :=
  (rfl)

/-- **The operation on a composable string is the total operation.** Including the value of the
operation on a composable string into the total module gives the total operation on the included
morphisms. -/
@[simp]
theorem homInclusion_pathOperation {n : ℕ} (X : Fin (n + 1) → C) (d : Fin n → ℤ)
    (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    homInclusion (X 0) (X (Fin.last n))
        (𝒞.pathOperation X d x : homModule (R := R) (X 0) (X (Fin.last n))) =
      𝒞.m n fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (x i).1 := by
  rw [coe_pathOperation_apply]
  exact homInclusion_homProjection_of_mem_range
    ((𝒞.isPathCompatible_m n).mem_range_homInclusion X fun i ↦ (x i).1)

/-- `A∞` categories on a graded linear quiver are determined by their operations on composable
strings. -/
@[ext]
theorem ext_pathOperation {𝒞 𝒞' : AInfinityCategory R C}
    (h : ∀ (n : ℕ) (X : Fin (n + 1) → C), 𝒞.pathOperation X = 𝒞'.pathOperation X) :
    𝒞 = 𝒞' := by
  refine ext <| funext fun n ↦ (𝒞.isPathCompatible_m n).ext (𝒞'.isPathCompatible_m n) fun X x ↦ ?_
  have e := InternalGrading.multilinearMap_ext
    (f := (𝒞.m n).compLinearMap fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ))
    (g := (𝒞'.m n).compLinearMap fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ))
    (fun i ↦ grading (R := R) (X i.rev.castSucc) (X i.rev.succ)) fun d y hy ↦ by
      rw [MultilinearMap.compLinearMap_apply, MultilinearMap.compLinearMap_apply,
        ← 𝒞.homInclusion_pathOperation X d fun i ↦ ⟨y i, hy i⟩,
        ← 𝒞'.homInclusion_pathOperation X d fun i ↦ ⟨y i, hy i⟩, h]
  exact DFunLike.congr_fun e x

/-! ### The differential and the composition -/

/-- The **differential** `m₁` of the morphisms `X ⟶ Y` of an `A∞` category. -/
noncomputable def homDifferential (X Y : C) :
    homModule (R := R) X Y →ₗ[R] homModule (R := R) X Y :=
  homProjection X Y ∘ₗ 𝒞.differential ∘ₗ homInclusion X Y

/-- The differential of a morphism is the component of the unary operation of the included
morphism. -/
theorem homDifferential_apply (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.homDifferential X Y f = homProjection X Y (𝒞.m 1 ![homInclusion X Y f]) := by
  rw [homDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
    AInfinityAlgebra.differential_apply]

/-- The Hom differential is the unary operation on a composable string. -/
theorem homDifferential_eq_m (X : Fin 2 → C)
    (f : ∀ i : Fin 1, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    𝒞.homDifferential (X 0) (X (Fin.last 1)) (f 0) =
      homProjection (X 0) (X (Fin.last 1))
        (𝒞.m 1 fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i)) := by
  rw [homDifferential_apply]
  -- The only input has endpoints X₀ and X₁; enumerate it to identify the literal tuple.
  have h : (fun i : Fin 1 ↦ homInclusion (R := R) (X i.rev.castSucc) (X i.rev.succ)
      (f i)) = ![homInclusion (X 0) (X (Fin.last 1)) (f 0)] := by
    funext i
    fin_cases i
    rfl
  rw [h]

/-- The differential of a morphism, included into the total module, is the unary operation of
the included morphism. -/
@[simp]
theorem homInclusion_homDifferential (X Y : C) (f : homModule (R := R) X Y) :
    homInclusion X Y (𝒞.homDifferential X Y f) =
      𝒞.differential (homInclusion X Y f) := by
  rw [AInfinityAlgebra.differential_apply, homDifferential_apply]
  apply homInclusion_homProjection_of_mem_range
  have h := (𝒞.isPathCompatible_m 1).mem_range_homInclusion ![X, Y]
    (Fin.cases (motive := fun i ↦ homModule (R := R) (![X, Y] i.rev.castSucc) (![X, Y] i.rev.succ))
      f fun i ↦ i.elim0)
  have e : (fun i : Fin 1 ↦ homInclusion (R := R) (![X, Y] i.rev.castSucc) (![X, Y] i.rev.succ)
      (Fin.cases (motive := fun i ↦ homModule (R := R) (![X, Y] i.rev.castSucc)
        (![X, Y] i.rev.succ)) f (fun i ↦ i.elim0) i)) = ![homInclusion X Y f] := by
    funext i
    fin_cases i
    rfl
  rwa [e] at h

/-- Taking a component intertwines the total differential with the Hom differential.
In particular, it sends total boundaries to boundaries in the selected Hom module. -/
theorem homProjection_differential (X Y : C) (x : TotalHom R C) :
    homProjection X Y (𝒞.differential x) =
      𝒞.homDifferential X Y (homProjection X Y x) := by
  classical
  suffices h : homProjection X Y ∘ₗ 𝒞.differential =
      𝒞.homDifferential X Y ∘ₗ homProjection X Y from LinearMap.congr_fun h x
  apply DirectSum.linearMap_ext
  intro p
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply]
  rw [← homInclusion_eq_lof p.1 p.2, ← homInclusion_homDifferential]
  by_cases h : p = (X, Y)
  · subst p
    simp only [homProjection_homInclusion]
  · rw [homProjection_homInclusion_of_ne h, homProjection_homInclusion_of_ne h, map_zero]

/-- The differential of an `A∞` category raises the degree by one. -/
theorem homDifferential_mem_piece {X Y : C} {p : ℤ} {f : homModule (R := R) X Y}
    (hf : f ∈ (grading (R := R) X Y).piece p) :
    𝒞.homDifferential X Y f ∈ (grading (R := R) X Y).piece (p + 1) := by
  rw [← homInclusion_mem_totalGrading_piece_iff, homInclusion_homDifferential,
    AInfinityAlgebra.differential_apply]
  simpa using 𝒞.m_mem_totalGrading_piece ![p] _
    (by simpa [Fin.forall_fin_one] using hf)

/-- **The differential of an `A∞` category squares to zero.** -/
@[simp]
theorem homDifferential_homDifferential (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.homDifferential X Y (𝒞.homDifferential X Y f) = 0 := by
  apply homInclusion_injective X Y
  rw [homInclusion_homDifferential, homInclusion_homDifferential, map_zero,
    AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply]
  exact 𝒞.stasheff_arity_one _

/-- The **composition** `m₂` of an `A∞` category: `𝒞.comp X Y Z g f` is the composite
`g ∘ f : X ⟶ Z` of `g : Y ⟶ Z` and `f : X ⟶ Y`. -/
noncomputable def comp (X Y Z : C) :
    homModule (R := R) Y Z →ₗ[R] homModule (R := R) X Y →ₗ[R] homModule (R := R) X Z :=
  LinearMap.compr₂ (𝒞.mul.compl₁₂ (homInclusion Y Z) (homInclusion X Y)) (homProjection X Z)

/-- The composite of two morphisms is the component of the binary operation of the included
morphisms. -/
theorem comp_apply (X Y Z : C) (g : homModule (R := R) Y Z) (f : homModule (R := R) X Y) :
    𝒞.comp X Y Z g f = homProjection X Z (𝒞.m 2 ![homInclusion Y Z g, homInclusion X Y f]) := by
  rw [comp, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, AInfinityAlgebra.mul_apply]

/-- Hom composition is the binary operation on a composable string, in Keller's input order. -/
theorem comp_eq_m (X : Fin 3 → C)
    (f : ∀ i : Fin 2, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    𝒞.comp (X 0) (X 1) (X (Fin.last 2)) (f 0) (f 1) =
      homProjection (X 0) (X (Fin.last 2))
        (𝒞.m 2 fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i)) := by
  rw [comp_apply]
  -- Reversal puts X₁ ⟶ X₂ first and X₀ ⟶ X₁ second; check both tuple entries explicitly.
  have h : (fun i : Fin 2 ↦ homInclusion (R := R) (X i.rev.castSucc) (X i.rev.succ)
      (f i)) = ![homInclusion (X 1) (X (Fin.last 2)) (f 0), homInclusion (X 0) (X 1) (f 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [h]

/-- The composite of two morphisms, included into the total module, is the binary operation of
the included morphisms. -/
@[simp]
theorem homInclusion_comp (X Y Z : C) (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y) :
    homInclusion X Z (𝒞.comp X Y Z g f) = 𝒞.m 2 ![homInclusion Y Z g, homInclusion X Y f] := by
  rw [comp_apply]
  apply homInclusion_homProjection_of_mem_range
  have h := (𝒞.isPathCompatible_m 2).mem_range_homInclusion ![X, Y, Z]
    (Fin.cases (motive := fun i ↦
        homModule (R := R) (![X, Y, Z] i.rev.castSucc) (![X, Y, Z] i.rev.succ))
      g (Fin.cases f fun i ↦ i.elim0))
  have e : (fun i : Fin 2 ↦ homInclusion (R := R) (![X, Y, Z] i.rev.castSucc)
      (![X, Y, Z] i.rev.succ) (Fin.cases (motive := fun i ↦
        homModule (R := R) (![X, Y, Z] i.rev.castSucc) (![X, Y, Z] i.rev.succ))
      g (Fin.cases f fun i ↦ i.elim0) i)) = ![homInclusion Y Z g, homInclusion X Y f] := by
    funext i
    fin_cases i <;> rfl
  rwa [e] at h

/-- The composite of morphisms of degrees `p` and `q` has degree `p + q`. -/
theorem comp_mem_piece {X Y Z : C} {p q : ℤ} {g : homModule (R := R) Y Z}
    {f : homModule (R := R) X Y} (hg : g ∈ (grading (R := R) Y Z).piece p)
    (hf : f ∈ (grading (R := R) X Y).piece q) :
    𝒞.comp X Y Z g f ∈ (grading (R := R) X Z).piece (p + q) := by
  rw [← homInclusion_mem_totalGrading_piece_iff, homInclusion_comp]
  simpa using 𝒞.m_mem_totalGrading_piece ![p, q] _
    (by simpa [Fin.forall_fin_two] using ⟨hg, hf⟩)

/-- **The Leibniz rule.** For `g : Y ⟶ Z` of degree `p` and `f : X ⟶ Y`, the differential of
`g ∘ f` is `d g ∘ f + (-1)^p g ∘ d f`. -/
theorem homDifferential_comp {X Y Z : C} {p : ℤ} {g : homModule (R := R) Y Z}
    (hg : g ∈ (grading (R := R) Y Z).piece p) (f : homModule (R := R) X Y) :
    𝒞.homDifferential X Z (𝒞.comp X Y Z g f) =
      𝒞.comp X Y Z (𝒞.homDifferential Y Z g) f +
        negOnePowCast R p • 𝒞.comp X Y Z g (𝒞.homDifferential X Y f) := by
  apply homInclusion_injective X Z
  rw [map_add, map_smul]
  simp only [homInclusion_homDifferential, homInclusion_comp,
    AInfinityAlgebra.differential_apply]
  exact 𝒞.stasheff_arity_two _ _ p (by rwa [𝒞.grading_eq, homInclusion_mem_totalGrading_piece_iff])

end AInfinityCategory

end TauCeti
