/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.Algebra.GroupAction.DiagonalOrbits
import TauCeti.RepresentationTheory.OfMulAction

/-!
# Hecke algebras of permutation modules

Let a group `G` act on a set `S` and let `A` be a commutative ring. The **permutation Hecke
module** `Fun_G(S × S, A)` consists of the functions `h : S × S → A` invariant under the diagonal
action of `G` whose support is a finite union of `G`-orbits. When every orbit of every point
stabilizer on `S` is finite (`TauCeti.FiniteStabilizerOrbits`), for instance when `G` is a
topological group and the point stabilizers are compact and open, such an `h` has finitely many
nonzero entries in each row and each column. It then acts on the permutation module `S →₀ A` by
`h * s = Σ_t h(t, s) t`, commuting with the permutation action of `G`, and the matrix product
`(h₁ * h₂)(x, z) = Σ_y h₁(x, y) h₂(y, z)` is a finite sum which corresponds to composition. This
makes `Fun_G(S × S, A)` a non-unital `A`-algebra.

Read through the coefficients `MonoidAlgebra.coeffLinearEquiv`, this action is by intertwining
maps of the permutation representation `Representation.ofMulAction A G S` on `A[S]`. When `S` has
finitely many `G`-orbits, the diagonal indicator is the unit, and
`TauCeti.PermutationHecke.toIntertwiningMapAlgEquiv` identifies `Fun_G(S × S, A)` with the algebra
`End_G(A[S])` of these intertwining maps.

No measure is used, so the construction works over every coefficient ring.

## Main declarations

* `TauCeti.permutationHeckeModule G S A`: the `A`-module `Fun_G(S × S, A)`, containing each
  orbit indicator (`TauCeti.PermutationHecke.indicator_orbit_mem`).
* `TauCeti.PermutationHecke.toEnd`: the action of `Fun_G(S × S, A)` on `S →₀ A`, with
  `toEnd_single` (`h * s = Σ_t h(t, s) t`), `toEnd_single_eq` and `toEnd_injective`.
* `TauCeti.PermutationHecke.toIntertwiningMap`: the same action on `A[S]`, by intertwining maps of
  `Representation.ofMulAction A G S`, with `toIntertwiningMap_single`.
* `TauCeti.PermutationHecke.mul_apply`: the matrix product, with `toEnd_mul`.
* `TauCeti.PermutationHecke.one_apply`, `TauCeti.PermutationHecke.algebraMap_apply`,
  `TauCeti.PermutationHecke.toIntertwiningMapAlgEquiv`: for finitely many orbits, the unit, the
  scalar matrices and the algebra isomorphism with `End_G(A[S])`.

## References

* D. Treumann and A. Venkatesh, *Functoriality, Smith theory, and the Brauer homomorphism*,
  Ann. of Math. 183 (2016), §2.10, (2.10.1)–(2.10.3), pp. 187–188 (arXiv:1407.2346v1 §2.10).
  The source displays the action as `Σ_t h(s, t) t`, which with the product (2.10.1) is a right
  action; this file uses the left action `Σ_t h(t, s) t`.
-/

public section
noncomputable section

open MulAction

namespace TauCeti

variable (G S : Type*) [Group G] [MulAction G S] (A : Type*) [CommRing A]

/-- The **permutation Hecke module** `Fun_G(S × S, A)`: functions `S × S → A` invariant under the
diagonal action of `G` whose support is a finite union of `G`-orbits. -/
def permutationHeckeModule : Submodule A (S × S → A) where
  carrier := {h | (∀ (g : G) (p : S × S), h (g • p) = h p) ∧
    (Quotient.mk (orbitRel G (S × S)) '' Function.support h).Finite}
  zero_mem' := ⟨fun _ _ ↦ rfl, by simp⟩
  add_mem' {h₁ h₂} h₁h h₂h := by
    refine ⟨fun g p ↦ by simp [h₁h.1 g p, h₂h.1 g p], (h₁h.2.union h₂h.2).subset ?_⟩
    rw [← Set.image_union]
    exact Set.image_mono (Function.support_add _ _)
  smul_mem' c h hh := by
    refine ⟨fun g p ↦ by simp [hh.1 g p], hh.2.subset (Set.image_mono ?_)⟩
    exact Function.support_const_smul_subset c h

variable {G S A}

namespace PermutationHecke

/-- Membership in `Fun_G(S × S, A)`. -/
theorem mem_iff {h : S × S → A} :
    h ∈ permutationHeckeModule G S A ↔ (∀ (g : G) (p : S × S), h (g • p) = h p) ∧
      (Quotient.mk (orbitRel G (S × S)) '' Function.support h).Finite :=
  Iff.rfl

/-- The indicator of a diagonal orbit lies in `Fun_G(S × S, A)`. -/
theorem indicator_orbit_mem (p : S × S) :
    Set.indicator (orbit G p) 1 ∈ permutationHeckeModule G S A := by
  refine ⟨fun g q ↦ ?_, (Set.finite_singleton (Quotient.mk (orbitRel G (S × S)) p)).subset ?_⟩
  · simp only [Set.indicator, Pi.one_apply, ← orbit_eq_iff, orbit_smul]
  rintro _ ⟨q, hq, rfl⟩
  exact Quotient.sound (Set.mem_of_indicator_ne_zero hq)

/-- Elements of `Fun_G(S × S, A)` are invariant under the diagonal action. -/
@[simp]
theorem apply_smul (h : permutationHeckeModule G S A) (g : G) (x y : S) :
    (h : S × S → A) (g • x, g • y) = (h : S × S → A) (x, y) :=
  h.property.1 g (x, y)

/-! ### Rows and columns -/

section Finiteness

variable [FiniteStabilizerOrbits G S]

omit [FiniteStabilizerOrbits G S] in
/-- The entries of `h` along a map `f : S → S × S` that meets each orbit in finitely many points
have finite support. -/
private theorem finite_support_comp (h : permutationHeckeModule G S A) (f : S → S × S)
    (hf : ∀ q, {y | Quotient.mk (orbitRel G (S × S)) (f y) = q}.Finite) :
    (Function.support fun y ↦ (h : S × S → A) (f y)).Finite :=
  (h.property.2.biUnion fun q _ ↦ hf q).subset fun y hy ↦ Set.mem_biUnion ⟨f y, hy, rfl⟩ rfl

/-- Each row of an element of `Fun_G(S × S, A)` has finitely many nonzero entries. -/
theorem finite_support_row (h : permutationHeckeModule G S A) (x : S) :
    (Function.support fun y ↦ (h : S × S → A) (x, y)).Finite :=
  finite_support_comp h _ (FiniteStabilizerOrbits.finite_setOf_mk_right_eq x)

/-- Each column of an element of `Fun_G(S × S, A)` has finitely many nonzero entries. -/
theorem finite_support_column (h : permutationHeckeModule G S A) (s : S) :
    (Function.support fun t ↦ (h : S × S → A) (t, s)).Finite :=
  finite_support_comp h _ (FiniteStabilizerOrbits.finite_setOf_mk_left_eq s)

/-- The column of `h` at `s`, the finitely supported function `t ↦ h(t, s)`. -/
def column (h : permutationHeckeModule G S A) (s : S) : S →₀ A :=
  Finsupp.ofSupportFinite (fun t ↦ (h : S × S → A) (t, s)) (finite_support_column h s)

/-- The entries of a column. -/
@[simp]
theorem column_apply (h : permutationHeckeModule G S A) (s t : S) :
    column h s t = (h : S × S → A) (t, s) :=
  (rfl)

/-! ### The action on the permutation module -/

variable (G S A) in
/-- The action of `Fun_G(S × S, A)` on the permutation module `S →₀ A`: `h` sends the basis
vector `s` to `Σ_t h(t, s) t`. -/
def toEnd : permutationHeckeModule G S A →ₗ[A] Module.End A (S →₀ A) where
  toFun h := Finsupp.linearCombination A (column h)
  map_add' h₁ h₂ := Finsupp.lhom_ext fun s c ↦ by
    ext t
    simp [Finsupp.linearCombination_single, mul_add]
  map_smul' c h := Finsupp.lhom_ext fun s d ↦ by
    ext t
    simp [Finsupp.linearCombination_single, mul_left_comm]

/-- `h` sends the basis vector `s` to `Σ_t h(t, s) t`. -/
@[simp]
theorem toEnd_single (h : permutationHeckeModule G S A) (s t : S) (c : A) :
    toEnd G S A h (Finsupp.single s c) t = c * (h : S × S → A) (t, s) := by
  simp [toEnd, Finsupp.linearCombination_single]

/-- `h` sends `c • s` to `c` times the column of `h` at `s`. -/
theorem toEnd_single_eq (h : permutationHeckeModule G S A) (s : S) (c : A) :
    toEnd G S A h (Finsupp.single s c) = c • column h s := by
  simp [toEnd, Finsupp.linearCombination_single]

/-- The action of `h` on a finitely supported function, as a finite sum. -/
theorem toEnd_apply (h : permutationHeckeModule G S A) (f : S →₀ A) (t : S) :
    toEnd G S A h f t = ∑ᶠ s, (h : S × S → A) (t, s) * f s := by
  rw [finsum_eq_sum_of_support_subset _ fun s hs ↦ Finsupp.mem_support_iff.mpr
    (right_ne_zero_of_mul (Function.mem_support.mp hs))]
  conv_lhs => rw [← f.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, toEnd_single]
  exact Finset.sum_congr rfl fun s _ ↦ mul_comm (f s) _

variable (G S A) in
/-- An element of `Fun_G(S × S, A)` is determined by its action on `S →₀ A`. -/
theorem toEnd_injective : Function.Injective (toEnd G S A) := by
  intro h₁ h₂ he
  refine Subtype.ext (funext fun p ↦ ?_)
  simpa using congrArg (fun φ : Module.End A (S →₀ A) ↦ φ (Finsupp.single p.2 1) p.1) he

variable (G S A) in
/-- The action of `Fun_G(S × S, A)` on the permutation representation `A[S]` of `G`, by
intertwining maps: `toEnd` read through the coefficients `MonoidAlgebra.coeffLinearEquiv`, so `h`
sends the basis vector `s` to `Σ_t h(t, s) t`. -/
def toIntertwiningMap : permutationHeckeModule G S A →ₗ[A]
    (Representation.ofMulAction A G S).IntertwiningMap (Representation.ofMulAction A G S) where
  toFun h :=
    { toLinearMap := (MonoidAlgebra.coeffLinearEquiv A).symm.toLinearMap ∘ₗ toEnd G S A h ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv A).toLinearMap
      isIntertwining' g := MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring <|
        MonoidAlgebra.coeff_injective <| Finsupp.ext fun t ↦ by
          simpa using (apply_smul h g⁻¹ t (g • s)).symm }
  map_add' h₁ h₂ := by ext; simp
  map_smul' c h := by ext; simp

/-- `toIntertwiningMap` is `toEnd` on coefficients. -/
@[simp]
theorem coeff_toIntertwiningMap_apply (h : permutationHeckeModule G S A) (f : MonoidAlgebra A S) :
    (toIntertwiningMap G S A h f).coeff = toEnd G S A h f.coeff :=
  (rfl)

/-- `h` sends the basis vector `c • s` of `A[S]` to `Σ_t c h(t, s) t`. -/
theorem toIntertwiningMap_single (h : permutationHeckeModule G S A) (s : S) (c : A) :
    toIntertwiningMap G S A h (MonoidAlgebra.single s c) =
      (column h s).sum fun t a ↦ MonoidAlgebra.single t (c * a) := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext t
  simp +contextual [toEnd_single_eq, Finsupp.sum, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Finsupp.single_apply]

variable (G S A) in
/-- An element of `Fun_G(S × S, A)` is determined by its action on `A[S]`. -/
theorem toIntertwiningMap_injective : Function.Injective (toIntertwiningMap G S A) := by
  refine fun h₁ h₂ he ↦ toEnd_injective G S A (LinearMap.ext fun f ↦ ?_)
  simpa using congrArg MonoidAlgebra.coeff
    (DFunLike.congr_fun he (MonoidAlgebra.ofCoeff f))

/-! ### The matrix product -/

/-- The matrix product `(x, z) ↦ Σ_y h₁(x, y) h₂(y, z)` of two elements of `Fun_G(S × S, A)`
lies in `Fun_G(S × S, A)`. -/
theorem finsum_mul_mem (h₁ h₂ : permutationHeckeModule G S A) :
    (fun p : S × S ↦ ∑ᶠ y, (h₁ : S × S → A) (p.1, y) * (h₂ : S × S → A) (y, p.2)) ∈
      permutationHeckeModule G S A := by
  refine ⟨fun g p ↦ ?_, ?_⟩
  · simp only [Prod.smul_fst, Prod.smul_snd]
    rw [← finsum_comp_equiv (MulAction.toPerm g)]
    exact finsum_congr fun y ↦ by rw [MulAction.toPerm_apply, apply_smul, apply_smul]
  -- The orbit of `(x, z)` is that of `(x₁, g • z)`, where `(x₁, y₁)` represents the orbit of a
  -- pair `(x, y)` in the support of `h₁`, and `g • z` lies in the finite row of `h₂` at `y₁`.
  let rep (q : Quotient (orbitRel G (S × S))) : S × S := q.out
  refine (h₁.property.2.biUnion fun q _ ↦ ((finite_support_row h₂ (rep q).2).image
    fun w ↦ Quotient.mk (orbitRel G (S × S)) ((rep q).1, w))).subset ?_
  rintro _ ⟨⟨x, z⟩, hxz, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, (h₁ : S × S → A) (x, y) * (h₂ : S × S → A) (y, z) ≠ 0 := by
    by_contra! hall
    exact hxz (finsum_eq_zero_of_forall_eq_zero hall)
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G (S × S)) (x, y)
  refine Set.mem_biUnion ⟨(x, y), left_ne_zero_of_mul hy, rfl⟩ ⟨g • z, ?_, ?_⟩
  · simp only [Function.mem_support, rep, ← hg, Prod.smul_snd, apply_smul]
    exact right_ne_zero_of_mul hy
  · refine Quotient.sound ⟨g, ?_⟩
    simp only [rep, ← hg, Prod.smul_mk]

/-- The matrix product `(h₁ * h₂)(x, z) = Σ_y h₁(x, y) h₂(y, z)` on `Fun_G(S × S, A)`. -/
instance instMulPermutationHeckeModule : Mul (permutationHeckeModule G S A) where
  mul h₁ h₂ := ⟨_, finsum_mul_mem h₁ h₂⟩

/-- The matrix product, entrywise. Only finitely many terms are nonzero. -/
theorem mul_apply (h₁ h₂ : permutationHeckeModule G S A) (x z : S) :
    ((h₁ * h₂ : permutationHeckeModule G S A) : S × S → A) (x, z) =
      ∑ᶠ y, (h₁ : S × S → A) (x, y) * (h₂ : S × S → A) (y, z) :=
  (rfl)

/-- The matrix product corresponds to composition of the actions on `S →₀ A`. -/
@[simp]
theorem toEnd_mul (h₁ h₂ : permutationHeckeModule G S A) :
    toEnd G S A (h₁ * h₂) = toEnd G S A h₁ * toEnd G S A h₂ := by
  refine Finsupp.lhom_ext fun z c ↦ ?_
  ext x
  rw [mul_apply_eq_comp, toEnd_single, mul_apply, toEnd_apply,
    mul_finsum' _ _ ((finite_support_row h₁ x).subset fun y hy ↦ left_ne_zero_of_mul hy)]
  refine finsum_congr fun y ↦ ?_
  rw [toEnd_single]
  ring

/-- The matrix product corresponds to composition of the actions on `A[S]`. -/
@[simp]
theorem toIntertwiningMap_mul (h₁ h₂ : permutationHeckeModule G S A) :
    toIntertwiningMap G S A (h₁ * h₂) = toIntertwiningMap G S A h₁ * toIntertwiningMap G S A h₂ :=
  Representation.IntertwiningMap.ext <| LinearMap.ext fun f ↦ MonoidAlgebra.coeff_injective <| by
    simp [toEnd_mul]

/-- The matrix product makes `Fun_G(S × S, A)` a non-unital ring. -/
instance instNonUnitalRingPermutationHeckeModule :
    NonUnitalRing (permutationHeckeModule G S A) :=
  (toEnd_injective G S A).nonUnitalRing _ (map_zero _) (map_add _) toEnd_mul
    (map_neg (toEnd G S A)) (map_sub (toEnd G S A))
    (fun _ _ ↦ by exact map_nsmul (toEnd G S A) _ _) fun _ _ ↦ by exact map_zsmul (toEnd G S A) _ _

instance instIsScalarTowerPermutationHeckeModule :
    IsScalarTower A (permutationHeckeModule G S A) (permutationHeckeModule G S A) where
  smul_assoc c h₁ h₂ := toEnd_injective G S A <| by
    simp only [smul_eq_mul, toEnd_mul, map_smul, smul_mul_assoc]

instance instSMulCommClassPermutationHeckeModule :
    SMulCommClass A (permutationHeckeModule G S A) (permutationHeckeModule G S A) where
  smul_comm c h₁ h₂ := toEnd_injective G S A <| by
    simp only [smul_eq_mul, toEnd_mul, map_smul, mul_smul_comm]

/-! ### Finitely many orbits -/

section FiniteOrbits

variable [Finite (orbitRel.Quotient G S)]

omit [FiniteStabilizerOrbits G S] in
/-- The diagonal indicator lies in `Fun_G(S × S, A)` when `S` has finitely many orbits. -/
theorem diagonal_mem :
    (fun p : S × S ↦ Finsupp.single p.2 (1 : A) p.1) ∈ permutationHeckeModule G S A := by
  refine ⟨fun g p ↦ Finsupp.single_apply_left (MulAction.injective g) _ _ _, ?_⟩
  refine (Set.finite_range fun q : orbitRel.Quotient G S ↦
    Quotient.mk (orbitRel G (S × S)) (q.out, q.out)).subset ?_
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  obtain rfl : x = y := (Finsupp.single_apply_ne_zero.mp hxy).1
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G S) x
  exact ⟨Quotient.mk _ x, Quotient.sound ⟨g, by simp [hg]⟩⟩

instance instOnePermutationHeckeModule : One (permutationHeckeModule G S A) where
  one := ⟨_, diagonal_mem⟩

omit [FiniteStabilizerOrbits G S] in
/-- The unit of `Fun_G(S × S, A)` is the diagonal indicator. -/
@[simp]
theorem one_apply (x y : S) :
    ((1 : permutationHeckeModule G S A) : S × S → A) (x, y) = Finsupp.single y 1 x :=
  (rfl)

/-- The unit acts as the identity. -/
@[simp]
theorem toEnd_one : toEnd G S A 1 = 1 := by
  refine Finsupp.lhom_ext fun s c ↦ ?_
  ext t
  classical
  simp [one_apply, Finsupp.single_apply]

instance instNatCastPermutationHeckeModule : NatCast (permutationHeckeModule G S A) where
  natCast n := n • 1

instance instIntCastPermutationHeckeModule : IntCast (permutationHeckeModule G S A) where
  intCast n := n • 1

instance instPowPermutationHeckeModule : Pow (permutationHeckeModule G S A) ℕ where
  pow h n := npowRec n h

omit [FiniteStabilizerOrbits G S] in
private theorem natCast_def (n : ℕ) : (n : permutationHeckeModule G S A) = n • 1 :=
  (rfl)

omit [FiniteStabilizerOrbits G S] in
private theorem intCast_def (n : ℤ) : (n : permutationHeckeModule G S A) = n • 1 :=
  (rfl)

private theorem pow_zero_def (h : permutationHeckeModule G S A) : h ^ 0 = 1 :=
  (rfl)

private theorem pow_succ_def (h : permutationHeckeModule G S A) (n : ℕ) :
    h ^ (n + 1) = h ^ n * h :=
  (rfl)

/-- The action of a power is the power of the action. -/
@[simp]
theorem toEnd_pow (h : permutationHeckeModule G S A) (n : ℕ) :
    toEnd G S A (h ^ n) = toEnd G S A h ^ n := by
  induction n with
  | zero => rw [pow_zero_def, toEnd_one, pow_zero]
  | succ n ih => rw [pow_succ_def, toEnd_mul, ih, pow_succ]

/-- The action of a natural number is multiplication by it. -/
@[simp]
theorem toEnd_natCast (n : ℕ) : toEnd G S A (n : permutationHeckeModule G S A) = n := by
  rw [natCast_def, map_nsmul, toEnd_one, nsmul_one]

/-- The action of an integer is multiplication by it. -/
@[simp]
theorem toEnd_intCast (n : ℤ) : toEnd G S A (n : permutationHeckeModule G S A) = n := by
  rw [intCast_def, map_zsmul, toEnd_one]
  exact zsmul_one (R := Module.End A (S →₀ A)) n

instance instRingPermutationHeckeModule : Ring (permutationHeckeModule G S A) :=
  (toEnd_injective G S A).ring _ (map_zero _) toEnd_one (map_add _) toEnd_mul
    (map_neg (toEnd G S A)) (map_sub (toEnd G S A))
    (fun _ _ ↦ by exact map_nsmul (toEnd G S A) _ _)
    (fun _ _ ↦ by exact map_zsmul (toEnd G S A) _ _)
    toEnd_pow toEnd_natCast toEnd_intCast

instance instAlgebraPermutationHeckeModule : Algebra A (permutationHeckeModule G S A) :=
  .ofModule smul_mul_assoc mul_smul_comm

/-- The scalar matrices: `algebraMap A _ c` is `c` on the diagonal and `0` off it. -/
@[simp]
theorem algebraMap_apply (c : A) (x y : S) :
    ((algebraMap A (permutationHeckeModule G S A) c : permutationHeckeModule G S A) :
      S × S → A) (x, y) = Finsupp.single y c x := by
  classical
  simp [Algebra.algebraMap_eq_smul_one, one_apply, Finsupp.single_apply]

variable (G S A) in
/-- The action of `Fun_G(S × S, A)` on `S →₀ A`, as an algebra homomorphism. -/
def toEndAlgHom : permutationHeckeModule G S A →ₐ[A] Module.End A (S →₀ A) :=
  AlgHom.ofLinearMap (toEnd G S A) toEnd_one toEnd_mul

/-- `toEndAlgHom` is `toEnd`. -/
@[simp]
theorem toEndAlgHom_apply (h : permutationHeckeModule G S A) :
    toEndAlgHom G S A h = toEnd G S A h :=
  (rfl)

/-- The unit acts as the identity on `A[S]`. -/
@[simp]
theorem toIntertwiningMap_one : toIntertwiningMap G S A 1 = 1 :=
  Representation.IntertwiningMap.ext <| LinearMap.ext fun f ↦ MonoidAlgebra.coeff_injective <| by
    simp [toEnd_one]

omit [FiniteStabilizerOrbits G S] in
/-- The matrix `(t, s) ↦ φ(s)(t)` of an intertwining map `φ` of `A[S]` lies in
`Fun_G(S × S, A)`. -/
theorem matrix_mem
    (φ : (Representation.ofMulAction A G S).IntertwiningMap (Representation.ofMulAction A G S)) :
    (fun p : S × S ↦ (φ (MonoidAlgebra.single p.2 1)).coeff p.1) ∈
      permutationHeckeModule G S A := by
  refine ⟨fun g p ↦ φ.coeff_ofMulAction_single_smul g p.2 p.1, ?_⟩
  -- A pair `(t, s)` is in the orbit of `(g • t, s₀)`, where `s₀` represents the orbit of `s`.
  refine (Set.finite_iUnion fun q : orbitRel.Quotient G S ↦
    (φ (MonoidAlgebra.single q.out 1)).coeff.support.finite_toSet.image
      fun t ↦ Quotient.mk (orbitRel G (S × S)) (t, q.out)).subset ?_
  rintro _ ⟨⟨t, s⟩, hts, rfl⟩
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G S) s
  refine Set.mem_iUnion.mpr ⟨Quotient.mk _ s, g • t, ?_, Quotient.sound ⟨g, by simp [hg]⟩⟩
  simp only at hg
  rwa [Finset.mem_coe, Finsupp.mem_support_iff, ← hg, φ.coeff_ofMulAction_single_smul]

/-- An intertwining map of `A[S]` is the action of its matrix. -/
theorem toIntertwiningMap_matrix
    (φ : (Representation.ofMulAction A G S).IntertwiningMap (Representation.ofMulAction A G S)) :
    toIntertwiningMap G S A ⟨_, matrix_mem φ⟩ = φ :=
  Representation.IntertwiningMap.ext <| MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring <|
    MonoidAlgebra.coeff_injective <| Finsupp.ext fun t ↦ by simp

variable (G S A) in
/-- **`Fun_G(S × S, A) ≃ End_G(A[S])`** when `S` has finitely many `G`-orbits: the action on the
permutation representation identifies the permutation Hecke algebra with the algebra of its
intertwining maps. -/
def toIntertwiningMapAlgEquiv : permutationHeckeModule G S A ≃ₐ[A]
    (Representation.ofMulAction A G S).IntertwiningMap (Representation.ofMulAction A G S) :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (toIntertwiningMap G S A) toIntertwiningMap_one toIntertwiningMap_mul)
    ⟨toIntertwiningMap_injective G S A, fun φ ↦ ⟨_, toIntertwiningMap_matrix φ⟩⟩

/-- The isomorphism `Fun_G(S × S, A) ≃ End_G(A[S])` is the action on `A[S]`. -/
@[simp]
theorem toIntertwiningMapAlgEquiv_apply (h : permutationHeckeModule G S A) :
    toIntertwiningMapAlgEquiv G S A h = toIntertwiningMap G S A h :=
  (rfl)

/-- The inverse of `toIntertwiningMapAlgEquiv` sends `φ` to its matrix `(t, s) ↦ φ(s)(t)`. -/
@[simp]
theorem toIntertwiningMapAlgEquiv_symm_apply
    (φ : (Representation.ofMulAction A G S).IntertwiningMap (Representation.ofMulAction A G S))
    (t s : S) :
    ((toIntertwiningMapAlgEquiv G S A).symm φ : S × S → A) (t, s) =
      (φ (MonoidAlgebra.single s 1)).coeff t := by
  rw [(toIntertwiningMapAlgEquiv G S A).symm_apply_eq.mpr (toIntertwiningMap_matrix φ).symm]

end FiniteOrbits

end Finiteness

end PermutationHecke

end TauCeti
