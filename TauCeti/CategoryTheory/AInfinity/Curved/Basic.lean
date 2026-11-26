/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Curved.Algebra
public import TauCeti.CategoryTheory.AInfinity.Basic
public import TauCeti.CategoryTheory.AInfinity.Stasheff

/-!
# Curved A-infinity categories

A curved nonunital **`A∞` category** on a graded linear quiver `C` over a commutative ring `R`
has, besides the operations

`mₙ : Hom(Xₙ₋₁, Xₙ) ⊗ ⋯ ⊗ Hom(X₀, X₁) ⟶ Hom(X₀, Xₙ)`

of degree `2 - n` for `n ≥ 1`, a **curvature** `m₀(X) ∈ Hom(X, X)` of degree two for every object
`X`. They satisfy the curved Stasheff identities on every composable string, the arity zero
included. Write such a string in the input order of the operations, as objects `X 0, …, X n` and
morphisms `xᵢ : X (i + 1) ⟶ X i`. The identity of arity `n` is the Stasheff identity
`TauCeti.AInfinity.stasheffSum` of the operations of positive arity plus the curvature insertions
`(-1) ^ p m_{n + 1}(x₀, …, x_{p - 1}, m₀(X p), x_p, …, x_{n - 1})`
(`TauCeti.AInfinity.curvatureInsertionSum`), where `X p` is the object between the inputs
`x_{p - 1}` and `x_p`. In arity zero the identity says that each curvature is a cycle,
`m₁(m₀(X)) = 0`; in arity one it says that for `a : X ⟶ Y`

`m₁(m₁(a)) + m₂(m₀(Y), a) - m₂(a, m₀(X)) = 0`,

so the unary operation squares to the difference of the curvatures acting on the two sides. The
endomorphisms of each object form a curved `A∞` algebra (`TauCeti.CurvedAInfinityAlgebra`) with
the curvature of the object. The Fukaya category of a symplectic manifold is a curved `A∞`
category whose curvature counts holomorphic discs with boundary on a Lagrangian and no inputs.

The curvature is a family of endomorphisms, one for each object, rather than a single element of
the total module of morphisms `⨁ (X, Y), Hom(X, Y)`: with infinitely many objects their sum is
not an element of the direct sum. So, unlike `TauCeti.AInfinityCategory`, a curved `A∞` category
is not stored as a curved `A∞` algebra on the total module. Its operations of positive arity are
stored on the total module and are path-compatible, and the curved Stasheff identities are
imposed on composable strings `X₀ ⟵ X₁ ⟵ ⋯ ⟵ Xₙ` only. On a string of morphisms which is not
composable, the Stasheff sum vanishes automatically.

The uncurved `A∞` categories are exactly the curved ones of zero curvature
(`TauCeti.AInfinityCategory.equivCurvatureEqZero`). In the other direction, the curved
identities on composable strings with zero curvature give the Stasheff identities on all inputs
(`TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_isPathCompatible`).

## Main definitions

* `TauCeti.CurvedAInfinityCategory`: a curved nonunital `A∞` category on a graded linear quiver.
* `TauCeti.AInfinityCategory.toCurvedAInfinityCategory`: an uncurved `A∞` category as a curved one
  of zero curvature.
* `TauCeti.CurvedAInfinityCategory.endAlgebra`: the curved `A∞` algebra of endomorphisms of an
  object.
* `TauCeti.CurvedAInfinityCategory.toAInfinityCategory`: a curved `A∞` category of zero curvature
  as an uncurved one.
* `TauCeti.AInfinityCategory.equivCurvatureEqZero`: uncurved `A∞` categories are the curved ones
  of zero curvature.

## Main results

* `TauCeti.CurvedAInfinityCategory.m_one_curvature`: the arity-zero identity `m₁(m₀(X)) = 0`.
* `TauCeti.CurvedAInfinityCategory.m_one_m_one`: the arity-one identity
  `m₁(m₁(a)) = m₂(a, m₀(X)) - m₂(m₀(Y), a)` for `a : X ⟶ Y`.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 3.2, for curved
  (filtered) `A∞` algebras.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1, for the
  operations and signs of `A∞` categories.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver AInfinity

/-- A curved nonunital **`A∞` category** on a graded linear quiver `C`: operations `m n` of degree
`2 - n` for `n ≥ 1` on the total module of morphisms `⨁ (X, Y), Hom(X, Y)`, path-compatible, and a
curvature `curvature X ∈ Hom(X, X)` of degree two for every object `X`, satisfying the curved
Stasheff identities on every homogeneous composable string `xᵢ : X (i + 1) ⟶ X i`, `i < n`. -/
structure CurvedAInfinityCategory (R : Type w) [CommRing R] (C : Type u)
    [GradedLinearQuiver.{u, v, w} R C] where
  /-- The unsuspended arity-`n` operation on the total module of morphisms. -/
  m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C)
  /-- The nullary operation on the total module vanishes: the curvature is the family
  `curvature`. -/
  m_zero : m 0 = 0
  /-- The operation `m n` of positive arity has cohomological degree `2 - n`. -/
  m_degree (n : ℕ) (hn : 0 < n) : MultilinearMap.IsHomogeneous (m n)
    (fun _ ↦ (totalGrading R C).piece) (totalGrading R C).piece (2 - n)
  /-- Every operation of positive arity sends composable strings to morphisms between their
  endpoints, and other strings to zero. -/
  isPathCompatible_m_of_pos (n : ℕ) (hn : 0 < n) : IsPathCompatible id (m n)
  /-- The curvature `m₀(X)` of the object `X`. -/
  curvature (X : C) : homModule (R := R) X X
  /-- The curvature has degree two. -/
  curvature_mem (X : C) : curvature X ∈ (grading (R := R) X X).piece 2
  /-- The curved Stasheff identities on homogeneous composable strings: the curvature inserted
  at position `p` is that of the object `X p` between the inputs `x (p - 1)` and `x p`. -/
  stasheff (n : ℕ) (X : ℕ → C) (d : ℕ → ℤ) (x : ℕ → TotalHom R C) :
    (∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (X (i + 1)) (X i))) →
      (∀ i < n, x i ∈ (totalGrading R C).piece (d i)) →
        stasheffSum m d x n +
          curvatureInsertionSum m x (fun p ↦ homInclusion (X p) (X p) (curvature (X p))) n = 0

namespace CurvedAInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- Curved `A∞` categories are determined by their operations and their curvature. -/
@[ext]
theorem ext {𝒞 𝒞' : CurvedAInfinityCategory R C} (hm : 𝒞.m = 𝒞'.m)
    (hc : 𝒞.curvature = 𝒞'.curvature) : 𝒞 = 𝒞' := by
  cases 𝒞
  cases 𝒞'
  simp only at hm hc
  subst hm hc
  rfl

variable (𝒞 : CurvedAInfinityCategory R C)

/-- Every operation of a curved `A∞` category sends composable strings to morphisms between their
endpoints, and other strings to zero. -/
theorem isPathCompatible_m (n : ℕ) : IsPathCompatible id (𝒞.m n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [𝒞.m_zero]
    exact ⟨fun _ _ ↦ zero_mem _, fun _ _ _ _ _ _ _ ↦ rfl⟩
  · exact 𝒞.isPathCompatible_m_of_pos n hn

/-- The operation `mₙ` sends inputs of degrees `dᵢ` to an element of degree `∑ dᵢ + 2 - n`. -/
theorem m_mem_totalGrading_piece {n : ℕ} (d : Fin n → ℤ) (x : Fin n → TotalHom R C)
    (hx : ∀ i, x i ∈ (totalGrading R C).piece (d i)) :
    𝒞.m n x ∈ (totalGrading R C).piece ((∑ i, d i) + (2 - n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝒞.m_zero]
  · exact (𝒞.m_degree n hn).map_mem d x hx

/-- **The arity-zero curved Stasheff identity**: the curvature of every object is a cycle,
`m₁(m₀(X)) = 0`. -/
@[simp]
theorem m_one_curvature (X : C) : 𝒞.m 1 ![homInclusion X X (𝒞.curvature X)] = 0 := by
  simpa using 𝒞.stasheff 0 (fun _ ↦ X) 0 0 (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    fun _ h ↦ absurd h (Nat.not_lt_zero _)

/-- **The arity-one curved Stasheff identity**: for a morphism `a : X ⟶ Y`, the unary operation
squares to `m₂(a, m₀(X)) - m₂(m₀(Y), a)`. -/
theorem m_one_m_one {X Y : C} (f : homModule (R := R) X Y) :
    𝒞.m 1 ![𝒞.m 1 ![homInclusion X Y f]] =
      𝒞.m 2 ![homInclusion X Y f, homInclusion X X (𝒞.curvature X)] -
        𝒞.m 2 ![homInclusion Y Y (𝒞.curvature Y), homInclusion X Y f] := by
  -- Both sides are linear in `f`, so it suffices to treat homogeneous morphisms.
  have h₀ (y : TotalHom R C) :
      Function.update ![0, homInclusion X X (𝒞.curvature X)] 0 y =
        ![y, homInclusion X X (𝒞.curvature X)] :=
    Fin.update_cons_zero ..
  let L : homModule (R := R) X Y →ₗ[R] TotalHom R C :=
    (𝒞.m 1).curryRight ![] ∘ₗ (𝒞.m 1).curryRight ![] ∘ₗ homInclusion X Y
  let Q : homModule (R := R) X Y →ₗ[R] TotalHom R C :=
    ((𝒞.m 2).toLinearMap ![0, homInclusion X X (𝒞.curvature X)] 0 -
      (𝒞.m 2).curryRight ![homInclusion Y Y (𝒞.curvature Y)]) ∘ₗ homInclusion X Y
  suffices L f = Q f by simpa [L, Q, h₀, MultilinearMap.curryRight_apply] using this
  refine LinearMap.congr_fun ((grading (R := R) X Y).linearMap_ext fun p g hg ↦ ?_) f
  -- The string `g : X ⟶ Y` runs through the objects `Y ⟵ X`; the object sequence below reduces
  -- to `Y` at position `0` and to `X` at position `1`, which `h'` uses by unfolding.
  have h := 𝒞.stasheff 1 (fun | 0 => Y | _ + 1 => X) (fun _ ↦ p) (fun _ ↦ homInclusion X Y g)
    (fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      exact LinearMap.mem_range_self _ g)
    (fun _ _ ↦ (homInclusion_mem_totalGrading_piece_iff _ _).2 hg)
  rw [stasheffSum_one, curvatureInsertionSum_one] at h
  have h' : 𝒞.m 1 ![𝒞.m 1 ![homInclusion X Y g]] =
      𝒞.m 2 ![homInclusion X Y g, homInclusion X X (𝒞.curvature X)] -
        𝒞.m 2 ![homInclusion Y Y (𝒞.curvature Y), homInclusion X Y g] := by
    rw [← neg_sub]
    exact eq_neg_of_add_eq_zero_left h
  simp [L, Q, h₀, MultilinearMap.curryRight_apply, h']

/-! ### The endomorphism algebra of an object -/

/-- The operations of the endomorphism algebra of `X`: the curvature of `X` in arity zero, and
the operations on the constant string at `X` in positive arity. -/
private noncomputable def endOperation (X : C) : ∀ n : ℕ,
    MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ homModule (R := R) X X) (homModule (R := R) X X)
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) _ (𝒞.curvature X)
  | n + 1 => (𝒞.m (n + 1)).restrictToPath id fun _ ↦ X

/-- In positive arity, the operations of the endomorphism algebra of `X` are those of the
category on the included endomorphisms. -/
private theorem homInclusion_endOperation (X : C) {n : ℕ} (hn : 0 < n)
    (y : Fin n → homModule (R := R) X X) :
    homInclusion X X (𝒞.endOperation X n y) = 𝒞.m n fun i ↦ homInclusion X X (y i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact (𝒞.isPathCompatible_m (n + 1)).homInclusion_restrictToPath (fun _ ↦ X) y

/-- The **endomorphism algebra** of an object `X` of a curved `A∞` category: the curved `A∞`
algebra on the endomorphisms of `X` whose curvature is the curvature of `X` and whose operations
of positive arity are those of the category on strings of endomorphisms of `X`. -/
noncomputable def endAlgebra (X : C) : CurvedAInfinityAlgebra R (homModule (R := R) X X) where
  grading := grading (R := R) X X
  m := 𝒞.endOperation X
  m_degree
    | 0 => MultilinearMap.isHomogeneous_def.2 fun d x _ ↦ by
      simpa [endOperation] using 𝒞.curvature_mem X
    | n + 1 => MultilinearMap.isHomogeneous_def.2 fun d y hy ↦ by
      rw [← homInclusion_mem_totalGrading_piece_iff, 𝒞.homInclusion_endOperation X n.succ_pos]
      exact 𝒞.m_mem_totalGrading_piece d _ fun i ↦
        (homInclusion_mem_totalGrading_piece_iff _ _).2 (hy i)
  stasheff n d x hx := by
    -- Include the endomorphisms into the total module, where the curvature of `X` becomes the
    -- nullary operation of the family `m'`.
    let m' := Function.update 𝒞.m 0
      (MultilinearMap.constOfIsEmpty (RingHom.id R) _ (homInclusion X X (𝒞.curvature X)))
    have hm' (k : ℕ) (hk : 0 < k) : m' k = 𝒞.m k := Function.update_of_ne hk.ne' _ _
    apply homInclusion_injective X X
    rw [map_zero, map_curvedStasheffSum _ _ _ (homInclusion X X) m' (fun k y ↦ ?_),
      curvedStasheffSum_eq_stasheffSum_add, sum_stasheffTerm_inner_zero,
      stasheffSum_congr_of_pos _ _ _ hm', curvatureInsertionSum_congr _ _ (hm' _ n.succ_pos)]
    · simpa [m'] using 𝒞.stasheff n (fun _ ↦ X) d (fun i ↦ homInclusion X X (x i))
        (fun i _ ↦ LinearMap.mem_range_self _ _)
        fun i hi ↦ (homInclusion_mem_totalGrading_piece_iff _ _).2 (hx i hi)
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [m', endOperation]
      · rw [hm' k hk, 𝒞.homInclusion_endOperation X hk]

@[simp]
theorem endAlgebra_grading (X : C) : (𝒞.endAlgebra X).grading = grading (R := R) X X := (rfl)

/-- The curvature of the endomorphism algebra of `X` is the curvature of `X`. -/
@[simp]
theorem curvature_endAlgebra (X : C) : (𝒞.endAlgebra X).curvature = 𝒞.curvature X :=
  ((𝒞.endAlgebra X).m_zero_apply ![]).symm

/-- In positive arity, the operations of the endomorphism algebra of `X` are those of the
category on the included endomorphisms. -/
theorem homInclusion_endAlgebra_m (X : C) {n : ℕ} (hn : 0 < n)
    (y : Fin n → homModule (R := R) X X) :
    homInclusion X X ((𝒞.endAlgebra X).m n y) = 𝒞.m n fun i ↦ homInclusion X X (y i) :=
  𝒞.homInclusion_endOperation X hn y

end CurvedAInfinityCategory

/-! ### Comparison with uncurved `A∞` categories -/

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- An uncurved `A∞` category is a curved `A∞` category with the same operations and zero
curvature: its curvature insertions vanish, and its curved Stasheff identities are its Stasheff
identities. -/
def toCurvedAInfinityCategory : CurvedAInfinityCategory R C where
  m := 𝒞.m
  m_zero := 𝒞.m_zero
  m_degree n hn := 𝒞.grading_eq ▸ 𝒞.m_degree n hn
  isPathCompatible_m_of_pos := 𝒞.isPathCompatible_m_of_pos
  curvature _ := 0
  curvature_mem _ := zero_mem _
  stasheff n _ d x _ hx := by
    simpa using 𝒞.stasheff n d x fun i hi ↦ 𝒞.grading_eq ▸ hx i hi

@[simp]
theorem toCurvedAInfinityCategory_m : 𝒞.toCurvedAInfinityCategory.m = 𝒞.m := (rfl)

/-- An uncurved `A∞` category has zero curvature. -/
@[simp]
theorem curvature_toCurvedAInfinityCategory (X : C) :
    𝒞.toCurvedAInfinityCategory.curvature X = 0 := (rfl)

end AInfinityCategory

namespace CurvedAInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : CurvedAInfinityCategory R C)

/-- With zero curvature, the curved Stasheff identities on composable strings give the Stasheff
identities on all homogeneous inputs. -/
private theorem stasheffSum_eq_zero (h : ∀ X, 𝒞.curvature X = 0) (n : ℕ) (hn : 0 < n)
    (d : ℕ → ℤ) (x : ℕ → TotalHom R C) (hx : ∀ i < n, x i ∈ (totalGrading R C).piece (d i)) :
    stasheffSum 𝒞.m d x n = 0 :=
  stasheffSum_eq_zero_of_isPathCompatible 𝒞.m_degree 𝒞.isPathCompatible_m_of_pos hn
    (fun X e y hy he ↦ by simpa [h] using 𝒞.stasheff n X e y hy he) d x hx

/-- A curved `A∞` category of zero curvature is an uncurved `A∞` category with the same
operations; its Taylor map is the suspension of the operations. -/
noncomputable def toAInfinityCategory (h : ∀ X, 𝒞.curvature X = 0) : AInfinityCategory R C where
  toAInfinityAlgebra := AInfinityAlgebra.ofStasheff (totalGrading R C) 𝒞.m 𝒞.m_zero 𝒞.m_degree
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    (𝒞.stasheffSum_eq_zero h)
  grading_eq := AInfinityAlgebra.ofStasheff_grading ..
  isPathCompatible_m_of_pos n hn := by
    rw [AInfinityAlgebra.ofStasheff_m]
    exact 𝒞.isPathCompatible_m_of_pos n hn

@[simp]
theorem toAInfinityCategory_m (h : ∀ X, 𝒞.curvature X = 0) :
    (𝒞.toAInfinityCategory h).m = 𝒞.m :=
  AInfinityAlgebra.ofStasheff_m ..

@[simp]
theorem toCurvedAInfinityCategory_toAInfinityCategory (h : ∀ X, 𝒞.curvature X = 0) :
    (𝒞.toAInfinityCategory h).toCurvedAInfinityCategory = 𝒞 :=
  ext (by simp) (funext fun X ↦ by simp [h])

end CurvedAInfinityCategory

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

@[simp]
theorem toAInfinityCategory_toCurvedAInfinityCategory (𝒞 : AInfinityCategory R C) :
    𝒞.toCurvedAInfinityCategory.toAInfinityCategory
      𝒞.curvature_toCurvedAInfinityCategory = 𝒞 :=
  AInfinityCategory.ext (by simp)

/-- **Uncurved `A∞` categories are the curved `A∞` categories of zero curvature.** -/
noncomputable def equivCurvatureEqZero :
    AInfinityCategory R C ≃ {𝒞 : CurvedAInfinityCategory R C // ∀ X, 𝒞.curvature X = 0} where
  toFun 𝒞 := ⟨𝒞.toCurvedAInfinityCategory, 𝒞.curvature_toCurvedAInfinityCategory⟩
  invFun 𝒞 := 𝒞.val.toAInfinityCategory 𝒞.property
  left_inv 𝒞 := 𝒞.toAInfinityCategory_toCurvedAInfinityCategory
  right_inv 𝒞 := Subtype.ext (𝒞.val.toCurvedAInfinityCategory_toAInfinityCategory 𝒞.property)

@[simp]
theorem coe_equivCurvatureEqZero_apply (𝒞 : AInfinityCategory R C) :
    (equivCurvatureEqZero 𝒞 : CurvedAInfinityCategory R C) = 𝒞.toCurvedAInfinityCategory := (rfl)

@[simp]
theorem equivCurvatureEqZero_symm_apply
    (𝒞 : {𝒞 : CurvedAInfinityCategory R C // ∀ X, 𝒞.curvature X = 0}) :
    equivCurvatureEqZero.symm 𝒞 = 𝒞.val.toAInfinityCategory 𝒞.property := (rfl)

end AInfinityCategory

end TauCeti
