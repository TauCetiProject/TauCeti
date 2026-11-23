/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Algebra.OpenSubgroup

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

When `S` has finitely many `G`-orbits, the diagonal indicator is the unit, and
`TauCeti.PermutationHecke.toEndAlgEquiv` identifies `Fun_G(S × S, A)` with the algebra
`End_G(A[S])` of `G`-equivariant endomorphisms, the centralizer of the permutation action.

No measure is used, so the construction works over every coefficient ring.

## Main declarations

* `TauCeti.FiniteStabilizerOrbits`: every orbit of every point stabilizer is finite, with
  `TauCeti.FiniteStabilizerOrbits.of_isCompact_of_isOpen` for compact open stabilizers.
* `TauCeti.permutationHeckeModule G S A`: the `A`-module `Fun_G(S × S, A)`.
* `TauCeti.PermutationHecke.toEnd`: the action of `Fun_G(S × S, A)` on `S →₀ A`, with
  `toEnd_single` (`h * s = Σ_t h(t, s) t`), `toEnd_injective` and `toEnd_comp_lmapDomain`
  (`G`-equivariance).
* `TauCeti.PermutationHecke.mul_apply`: the matrix product, with `toEnd_mul`.
* `TauCeti.PermutationHecke.one_apply`, `TauCeti.PermutationHecke.toEndAlgEquiv`: for finitely
  many orbits, the unit and the algebra isomorphism with `End_G(A[S])`.

## References

* Y. Tian and L. Xiao, *Tate cycles on some quaternionic Shimura varieties mod p*, Duke Math. J.
  168 (2019), §2.10, (2.10.1)–(2.10.3), pp. 187–188.
-/

public section
noncomputable section

open MulAction

namespace TauCeti

variable (G S : Type*) [Group G] [MulAction G S]

/-- Every orbit of every point stabilizer is finite: for all `x y : S`, the orbit of `y` under the
stabilizer of `x` is finite. This holds when `G` is a topological group and every point stabilizer
is compact and open (`TauCeti.FiniteStabilizerOrbits.of_isCompact_of_isOpen`). -/
class FiniteStabilizerOrbits : Prop where
  finite_orbit (x y : S) : (orbit (stabilizer G x) y).Finite

variable {G S}

/-- If every point stabilizer is compact and open, every orbit of every point stabilizer is
finite. -/
theorem FiniteStabilizerOrbits.of_isCompact_of_isOpen [TopologicalSpace G] [IsTopologicalGroup G]
    (hc : ∀ x : S, IsCompact (stabilizer G x : Set G))
    (ho : ∀ x : S, IsOpen (stabilizer G x : Set G)) : FiniteStabilizerOrbits G S where
  finite_orbit x y := by
    let K := stabilizer G x
    have : CompactSpace K := isCompact_iff_compactSpace.mp (hc x)
    have hopen : IsOpen (stabilizer K y : Set K) := (ho y).preimage continuous_subtypeVal
    have : Finite (K ⧸ stabilizer K y) := (stabilizer K y).quotient_finite_of_isOpen hopen
    exact Set.finite_coe_iff.mp (.of_equiv _ (orbitEquivQuotientStabilizer K y).symm)

variable (G S) (A : Type*) [CommRing A]

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

/-- Elements of `Fun_G(S × S, A)` are invariant under the diagonal action. -/
theorem apply_smul (h : permutationHeckeModule G S A) (g : G) (x y : S) :
    (h : S × S → A) (g • x, g • y) = (h : S × S → A) (x, y) :=
  h.property.1 g (x, y)

/-! ### Rows and columns -/

section Finiteness

variable [FiniteStabilizerOrbits G S]

/-- The points `y` with `(x, y)` in a given orbit form a finite set. -/
private theorem finite_setOf_mk_left_eq (x : S) (q : Quotient (orbitRel G (S × S))) :
    {y | Quotient.mk (orbitRel G (S × S)) (x, y) = q}.Finite := by
  rcases Set.eq_empty_or_nonempty {y | Quotient.mk (orbitRel G (S × S)) (x, y) = q} with
    h | ⟨y₀, hy₀⟩
  · simp [h]
  refine (FiniteStabilizerOrbits.finite_orbit (G := G) x y₀).subset fun y hy ↦ ?_
  obtain ⟨g, hg⟩ := Quotient.exact (hy.trans hy₀.symm)
  simp only [Prod.smul_mk, Prod.mk.injEq] at hg
  exact ⟨⟨g, hg.1⟩, hg.2⟩

/-- The points `t` with `(t, s)` in a given orbit form a finite set. -/
private theorem finite_setOf_mk_right_eq (s : S) (q : Quotient (orbitRel G (S × S))) :
    {t | Quotient.mk (orbitRel G (S × S)) (t, s) = q}.Finite := by
  rcases Set.eq_empty_or_nonempty {t | Quotient.mk (orbitRel G (S × S)) (t, s) = q} with
    h | ⟨t₀, ht₀⟩
  · simp [h]
  refine (FiniteStabilizerOrbits.finite_orbit (G := G) s t₀).subset fun t ht ↦ ?_
  obtain ⟨g, hg⟩ := Quotient.exact (ht.trans ht₀.symm)
  simp only [Prod.smul_mk, Prod.mk.injEq] at hg
  exact ⟨⟨g, hg.2⟩, hg.1⟩

/-- Each row of an element of `Fun_G(S × S, A)` has finitely many nonzero entries. -/
theorem finite_support_row (h : permutationHeckeModule G S A) (x : S) :
    (Function.support fun y ↦ (h : S × S → A) (x, y)).Finite := by
  refine (h.property.2.biUnion fun q _ ↦ finite_setOf_mk_left_eq x q).subset fun y hy ↦ ?_
  exact Set.mem_biUnion ⟨(x, y), hy, rfl⟩ rfl

/-- Each column of an element of `Fun_G(S × S, A)` has finitely many nonzero entries. -/
theorem finite_support_column (h : permutationHeckeModule G S A) (s : S) :
    (Function.support fun t ↦ (h : S × S → A) (t, s)).Finite := by
  refine (h.property.2.biUnion fun q _ ↦ finite_setOf_mk_right_eq s q).subset fun t ht ↦ ?_
  exact Set.mem_biUnion ⟨(t, s), ht, rfl⟩ rfl

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

/-- The action of `Fun_G(S × S, A)` commutes with the permutation action of `G` on `S →₀ A`. -/
theorem toEnd_comp_lmapDomain (h : permutationHeckeModule G S A) (g : G) :
    toEnd G S A h ∘ₗ Finsupp.lmapDomain A A (g • · : S → S) =
      Finsupp.lmapDomain A A (g • · : S → S) ∘ₗ toEnd G S A h := by
  refine Finsupp.lhom_ext fun s c ↦ ?_
  ext t
  have key := Finsupp.mapDomain_apply_of_injective (f := (g • · : S → S)) (MulAction.injective g)
    (toEnd G S A h (Finsupp.single s c)) (g⁻¹ • t)
  simp only [smul_inv_smul] at key
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, key, toEnd_single]
  rw [← apply_smul h g⁻¹, inv_smul_smul]

/-! ### The matrix product -/

/-- The matrix product `(h₁ * h₂)(x, z) = Σ_y h₁(x, y) h₂(y, z)` of two elements of
`Fun_G(S × S, A)`, as a function on `S × S`. -/
def mulFun (h₁ h₂ : permutationHeckeModule G S A) (p : S × S) : A :=
  ∑ᶠ y, (h₁ : S × S → A) (p.1, y) * (h₂ : S × S → A) (y, p.2)

/-- The matrix product of two elements of `Fun_G(S × S, A)` lies in `Fun_G(S × S, A)`. -/
theorem mulFun_mem (h₁ h₂ : permutationHeckeModule G S A) :
    mulFun h₁ h₂ ∈ permutationHeckeModule G S A := by
  refine ⟨fun g p ↦ ?_, ?_⟩
  · change ∑ᶠ y, (h₁ : S × S → A) (g • p.1, y) * (h₂ : S × S → A) (y, g • p.2) =
      ∑ᶠ y, (h₁ : S × S → A) (p.1, y) * (h₂ : S × S → A) (y, p.2)
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
  mul h₁ h₂ := ⟨mulFun h₁ h₂, mulFun_mem h₁ h₂⟩

/-- The matrix product, entrywise. Only finitely many terms are nonzero. -/
theorem mul_apply (h₁ h₂ : permutationHeckeModule G S A) (x z : S) :
    ((h₁ * h₂ : permutationHeckeModule G S A) : S × S → A) (x, z) =
      ∑ᶠ y, (h₁ : S × S → A) (x, y) * (h₂ : S × S → A) (y, z) :=
  (rfl)

/-- The matrix product corresponds to composition of the actions on `S →₀ A`. -/
theorem toEnd_mul (h₁ h₂ : permutationHeckeModule G S A) :
    toEnd G S A (h₁ * h₂) = toEnd G S A h₁ * toEnd G S A h₂ := by
  refine Finsupp.lhom_ext fun z c ↦ ?_
  ext x
  rw [mul_apply_eq_comp, toEnd_single, mul_apply, toEnd_apply,
    mul_finsum' _ _ ((finite_support_row h₁ x).subset fun y hy ↦ left_ne_zero_of_mul hy)]
  refine finsum_congr fun y ↦ ?_
  rw [toEnd_single]
  ring

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
theorem one_apply (x y : S) :
    ((1 : permutationHeckeModule G S A) : S × S → A) (x, y) = Finsupp.single y 1 x :=
  (rfl)

/-- The unit acts as the identity. -/
theorem toEnd_one : toEnd G S A 1 = 1 := by
  refine Finsupp.lhom_ext fun s c ↦ ?_
  ext t
  rw [toEnd_single, one_apply, one_apply_eq_self, ← smul_eq_mul, ← Finsupp.smul_apply,
    Finsupp.smul_single, smul_eq_mul, mul_one]

instance instNatCastPermutationHeckeModule : NatCast (permutationHeckeModule G S A) where
  natCast n := n • 1

instance instIntCastPermutationHeckeModule : IntCast (permutationHeckeModule G S A) where
  intCast n := n • 1

instance instPowPermutationHeckeModule : Pow (permutationHeckeModule G S A) ℕ where
  pow h n := npowRec n h

/-- The action of a power is the power of the action. -/
theorem toEnd_pow (h : permutationHeckeModule G S A) (n : ℕ) :
    toEnd G S A (h ^ n) = toEnd G S A h ^ n := by
  induction n with
  | zero => exact toEnd_one
  | succ n ih =>
    change toEnd G S A (h ^ n * h) = _
    rw [toEnd_mul, ih, pow_succ]

/-- The action of a natural number is multiplication by it. -/
theorem toEnd_natCast (n : ℕ) : toEnd G S A (n : permutationHeckeModule G S A) = n := by
  change toEnd G S A (n • 1) = _
  rw [map_nsmul, toEnd_one, nsmul_one]

/-- The action of an integer is multiplication by it. -/
theorem toEnd_intCast (n : ℤ) : toEnd G S A (n : permutationHeckeModule G S A) = n := by
  change toEnd G S A (n • 1) = _
  rw [map_zsmul, toEnd_one]
  exact zsmul_one (R := Module.End A (S →₀ A)) n

instance instRingPermutationHeckeModule : Ring (permutationHeckeModule G S A) :=
  (toEnd_injective G S A).ring _ (map_zero _) toEnd_one (map_add _) toEnd_mul
    (map_neg (toEnd G S A)) (map_sub (toEnd G S A))
    (fun _ _ ↦ by exact map_nsmul (toEnd G S A) _ _)
    (fun _ _ ↦ by exact map_zsmul (toEnd G S A) _ _)
    toEnd_pow toEnd_natCast toEnd_intCast

instance instAlgebraPermutationHeckeModule : Algebra A (permutationHeckeModule G S A) :=
  .ofModule smul_mul_assoc mul_smul_comm

variable (G S A) in
/-- The action of `Fun_G(S × S, A)` on `S →₀ A`, as an algebra homomorphism. -/
def toEndAlgHom : permutationHeckeModule G S A →ₐ[A] Module.End A (S →₀ A) :=
  AlgHom.ofLinearMap (toEnd G S A) toEnd_one toEnd_mul

variable (G S A) in
/-- `End_G(A[S])`: the endomorphisms of the permutation module `S →₀ A` commuting with the
permutation action of `G`. -/
abbrev equivariantEnd : Subalgebra A (Module.End A (S →₀ A)) :=
  Subalgebra.centralizer A (Set.range fun g : G ↦ Finsupp.lmapDomain A A (g • · : S → S))

omit [FiniteStabilizerOrbits G S] in
/-- The matrix `(t, s) ↦ φ(s)(t)` of an equivariant endomorphism `φ` lies in
`Fun_G(S × S, A)`. -/
theorem matrix_mem (φ : equivariantEnd G S A) :
    (fun p : S × S ↦ (φ : Module.End A (S →₀ A)) (Finsupp.single p.2 1) p.1) ∈
      permutationHeckeModule G S A := by
  have hφ (g : G) (f : S →₀ A) : (φ : Module.End A (S →₀ A)) (f.mapDomain (g • ·)) =
      ((φ : Module.End A (S →₀ A)) f).mapDomain (g • ·) :=
    (LinearMap.congr_fun (φ.property _ ⟨g, rfl⟩) f).symm
  refine ⟨fun g p ↦ ?_, ?_⟩
  · simp only [Prod.smul_fst, Prod.smul_snd]
    rw [← Finsupp.mapDomain_single (f := (g • · : S → S)), hφ,
      Finsupp.mapDomain_apply_of_injective (MulAction.injective g)]
  -- A pair `(t, s)` is in the orbit of `(g • t, s₀)`, where `s₀` represents the orbit of `s`.
  refine (Set.finite_iUnion fun q : orbitRel.Quotient G S ↦
    (((φ : Module.End A (S →₀ A)) (Finsupp.single q.out 1)).support.finite_toSet.image
      fun t ↦ Quotient.mk (orbitRel G (S × S)) (t, q.out))).subset ?_
  rintro _ ⟨⟨t, s⟩, hts, rfl⟩
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G S) s
  refine Set.mem_iUnion.mpr ⟨Quotient.mk _ s, g • t, ?_, Quotient.sound ⟨g, by simp [hg]⟩⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  simp only [Function.mem_support] at hts
  simp only at hg
  rwa [← hg, ← Finsupp.mapDomain_single (f := (g • · : S → S)), hφ,
    Finsupp.mapDomain_apply_of_injective (MulAction.injective g)]

variable (G S A) in
/-- **`Fun_G(S × S, A) ≃ End_G(A[S])`** when `S` has finitely many `G`-orbits: the action on the
permutation module identifies the permutation Hecke algebra with the equivariant endomorphisms. -/
def toEndAlgEquiv : permutationHeckeModule G S A ≃ₐ[A] equivariantEnd G S A :=
  AlgEquiv.ofBijective
    ((toEndAlgHom G S A).codRestrict _ fun h ↦ by
      rintro _ ⟨g, rfl⟩
      exact (toEnd_comp_lmapDomain h g).symm)
    ⟨fun h₁ h₂ he ↦ toEnd_injective G S A (congrArg Subtype.val he), fun φ ↦ ⟨⟨_, matrix_mem φ⟩,
      Subtype.ext <| Finsupp.lhom_ext fun s c ↦ by
        ext t
        change toEnd G S A ⟨_, matrix_mem φ⟩ (Finsupp.single s c) t = _
        rw [toEnd_single, ← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul,
          Finsupp.smul_single, smul_eq_mul, mul_one]⟩⟩

/-- The isomorphism `Fun_G(S × S, A) ≃ End_G(A[S])` is the action on `S →₀ A`. -/
@[simp]
theorem coe_toEndAlgEquiv_apply (h : permutationHeckeModule G S A) :
    (toEndAlgEquiv G S A h : Module.End A (S →₀ A)) = toEnd G S A h :=
  (rfl)

end FiniteOrbits

end Finiteness

end PermutationHecke

end TauCeti
