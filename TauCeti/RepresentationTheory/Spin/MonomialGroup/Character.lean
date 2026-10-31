/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup
public import TauCeti.RepresentationTheory.Induction.Restriction
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Spin.MonomialGroup.Spinor
-- Non-public: `IsPrimitiveRoot.neg_one_of_two_ne_zero` and `rootsOfUnity.isCyclic` supply the
-- square roots of unity of a field in which `2` is invertible.
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The characters of the group of signed monomials on which `ε` acts trivially

Let `b` be an orthogonal basis of a quadratic module `(M, Q)` whose generators square to `±1`,
indexed by a type with `n` elements. The group `CliffordAlgebra.monomialGroup Q b` of signed
monomials `±e_s`, its central element `ε = -1`, the sign subgroup `⟨ε⟩` it generates and the
quotient by that subgroup are built in `TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup`:
over a nontrivial coefficient ring in which `2` is invertible the group has `2 ^ (n + 1)` elements,
the sign subgroup has two, and the quotient is commutative with every element of order dividing
two and has `2 ^ n` elements. Every count below inherits those two hypotheses on the coefficient
ring `R`; in characteristic two `ε = 1`, the sign subgroup is trivial and the counts fail.

This file turns those group-theoretic facts into representation theory. A representation of the
group of signed monomials on which `ε` acts by the identity is the same as a representation of the
quotient. For a pairwise orthogonal family of generators and over an algebraically closed field,
such a representation is one-dimensional whenever it is finite-dimensional and irreducible, because
the quotient is commutative for such a family. The field of the representations and the
coefficient ring of the Clifford algebra are independent. The complementary sector, where `ε` acts
by `-1`, is the one `CliffordAlgebra.monomialGroupLift` identifies with the Clifford modules,
classified through the spinor module in `TauCeti.RepresentationTheory.Spin.MonomialGroup.Spinor`.

Since `ε` is central of order two, it acts on an irreducible representation by `1` or by `-1`.
For an orthogonal basis whose generators square to `±1`, the two halves above are assembled into
a classification. Any two signed monomials commute up to `ε` and every signed monomial squares to
`1` or `ε`, so in a representation in which `ε` acts by `1` the operators commute and square to the
identity. Schur's lemma makes each of them `±1` on an irreducible representation, over any field
and without any algebraic closure, finite dimension or finiteness of the basis, so such a
representation is the line of a character trivial on `ε`. For a finite basis and over a field of
characteristic not two, this character is exactly one of the `2 ^ n` sign characters
`CliffordAlgebra.monomialGroupCharacter hb hQ t : ±e_s ↦ (-1) ^ #(s ∩ t)`, and these are all the
characters trivial on `ε` with values in a domain of characteristic not two. Together with the
spinor classification this describes all the irreducible representations of the group over a
separably closed field of characteristic not two; in dimension one, for instance, all four of them
are one-dimensional.

## Main results

* `CliffordAlgebra.finrank_eq_one_of_apply_monomialGroupEpsilon_eq_one`: for a pairwise orthogonal
  family of generators and over an algebraically closed field, a finite-dimensional irreducible
  representation on which `ε` acts trivially is a line, and
  `CliffordAlgebra.ofLinearCharacter_comp_mk_apply_monomialGroupEpsilon` goes the other way, from a
  character of the quotient to a representation on which `ε` acts trivially.
* `CliffordAlgebra.natCard_monoidHom_quotient_monomialGroupSign`: for a finite orthogonal basis of
  `n` generators squaring to `±1` over a nontrivial ring in which `2` is invertible, and with values
  in a field in which `2` is invertible, the quotient has exactly `2 ^ n` characters.
* `CliffordAlgebra.natCard_monoidHom_monomialGroup_apply_monomialGroupEpsilon_eq_one`: with values
  in a domain of characteristic not two, the group of signed monomials has exactly `2 ^ n`
  characters sending `ε` to `1`, namely the sign characters `χ_t`.
* `TauCeti.monomialGroup_apply_monomialGroupEpsilon_eq_one_or_eq_neg_one`: `ε` acts on an
  irreducible representation by `1` or by `-1`.
* `TauCeti.monomialGroup_existsUnique_nonempty_equiv_ofLinearCharacter`: for a finite orthogonal
  basis whose generators square to `±1` and over a field of characteristic not two, an irreducible
  representation in which `ε` acts by `1` is equivalent to the line of the sign character `χ_t`
  for exactly one index set `t`.
* `TauCeti.monomialGroup_finrank_eq_one_of_apply_monomialGroupEpsilon_eq_one`: over any field, an
  irreducible representation in which `ε` acts by `1` is a line.
* `TauCeti.monomialGroup_finrank_eq_one_of_finrank_eq_one`: in dimension one, over a separably
  closed field, every irreducible representation is a line.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §3.1 for the
  characters of a finite abelian group.
-/

public section

namespace CliffordAlgebra

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
  (v : I → M)

/-! ### Irreducible representations on which `ε` acts trivially -/

/-- **A finite-dimensional irreducible representation of the group of signed monomials on which `ε`
acts trivially is a line**, for a pairwise orthogonal family of generators and over an algebraically
closed field. Such a representation factors through the quotient by the sign subgroup, which is
commutative for such a family, so Schur's lemma leaves no room for more than one dimension. -/
theorem finrank_eq_one_of_apply_monomialGroupEpsilon_eq_one
    (hv : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) {F W : Type*} [Field F] [IsAlgClosed F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F (monomialGroup Q v) W) [ρ.IsIrreducible]
    (hρ : ρ (monomialGroupEpsilon Q v) = 1) :
    Module.finrank F W = 1 := by
  have htriv : Representation.IsTrivial (ρ.comp (monomialGroupSign Q v).subtype) := by
    refine ⟨fun g ↦ ?_⟩
    rw [← Module.End.one_eq_id]
    rcases (mem_monomialGroupSign_iff v).mp g.2 with hg | hg
    · simp [hg]
    · simp [hg, hρ]
  have : IsMulCommutative (monomialGroup Q v ⧸ monomialGroupSign Q v) :=
    isMulCommutative_quotient_monomialGroupSign v hv
  have : (ρ.ofQuotient (monomialGroupSign Q v)).IsIrreducible :=
    (Representation.isIrreducible_ofQuotient_iff ρ (monomialGroupSign Q v)).mpr ‹ρ.IsIrreducible›
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    (ρ.ofQuotient (monomialGroupSign Q v))

/-- **Each character of the quotient by the sign subgroup gives a representation of the group of
signed monomials on which `ε` acts trivially.** The representation is the line carrying the
character of the class, `Representation.ofLinearCharacter`; over a field it is irreducible by
`Representation.isIrreducible_ofLinearCharacter`, and distinct characters give distinct
representations by `Representation.ofLinearCharacter_injective`. The identity itself needs no more
of the coefficients than a commutative semiring. -/
theorem ofLinearCharacter_comp_mk_apply_monomialGroupEpsilon {F : Type*} [CommSemiring F]
    (χ : (monomialGroup Q v ⧸ monomialGroupSign Q v) →* Fˣ) :
    Representation.ofLinearCharacter (χ.comp (QuotientGroup.mk' (monomialGroupSign Q v)))
      (monomialGroupEpsilon Q v) = 1 := by
  have hε := (QuotientGroup.eq_one_iff (N := monomialGroupSign Q v)
    (monomialGroupEpsilon Q v)).mpr (monomialGroupEpsilon_mem_monomialGroupSign v)
  refine LinearMap.ext fun x ↦ ?_
  simp [hε]

/-! ### The characters of the quotient -/

variable [Invertible (2 : R)] [LinearOrder I] {b : Module.Basis I R M}

/-- **The quotient by the sign subgroup has exactly `2 ^ n` characters** with values in a field in
which `2` is invertible: it is a finite commutative group of exponent dividing two with `2 ^ n`
elements, and such a group is isomorphic to its character group. -/
theorem natCard_monoidHom_quotient_monomialGroupSign [Fintype I] [Nontrivial R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    {F : Type*} [Field F] (hF : (2 : F) ≠ 0) :
    Nat.card ((monomialGroup Q b ⧸ monomialGroupSign Q b) →* Fˣ) = 2 ^ Fintype.card I := by
  have hortho : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j) := fun _ _ hij ↦
    QuadraticMap.associated_isOrtho.mp (hb hij)
  have : Finite (monomialGroup Q b) := finite_monomialGroup hb hQ
  have : HasEnoughRootsOfUnity F 2 :=
    { prim := ⟨-1, IsPrimitiveRoot.neg_one_of_two_ne_zero hF⟩, cyc := inferInstance }
  have : HasEnoughRootsOfUnity F
      (Monoid.exponent (monomialGroup Q b ⧸ monomialGroupSign Q b)) :=
    HasEnoughRootsOfUnity.of_dvd F (exponent_quotient_monomialGroupSign_dvd_two b hortho hQ)
  let hG : Group (monomialGroup Q b ⧸ monomialGroupSign Q b) := inferInstance
  let : CommGroup (monomialGroup Q b ⧸ monomialGroupSign Q b) :=
    { hG with
      mul_comm := isMulCommutative_iff.mp (isMulCommutative_quotient_monomialGroupSign b hortho) }
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ F,
    natCard_quotient_monomialGroupSign hb hQ]

/-- **There are `2 ^ n` characters trivial on `ε`**: for an orthogonal basis of `n` vectors whose
generators square to `±1`, the characters of the group of signed monomials with values in a domain
of characteristic not two that are trivial on `ε = -1` are the `2 ^ n` sign characters `χ_t`. -/
theorem natCard_monoidHom_monomialGroup_apply_monomialGroupEpsilon_eq_one [Fintype I] [Nontrivial R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (k : Type*) [CommRing k] [IsDomain k] [NeZero (2 : k)] :
    Nat.card {χ : monomialGroup Q b →* kˣ // χ (monomialGroupEpsilon Q b) = 1} =
      2 ^ Fintype.card I := by
  rw [← Fintype.card_finset, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (Equiv.ofBijective (fun t ↦
    ⟨(Units.map (Int.castRingHom k : ℤ →* k)).comp (monomialGroupCharacter hb hQ t), by simp⟩)
    ⟨fun t t' h ↦ ?_, fun χ ↦ ?_⟩)).symm
  · exact (existsUnique_monomialGroupCharacter_eq hb hQ _ (by simp)).unique rfl
      (congrArg Subtype.val h).symm
  · obtain ⟨t, ht, -⟩ := existsUnique_monomialGroupCharacter_eq hb hQ χ.1 χ.2
    exact ⟨t, Subtype.ext ht⟩

end CliffordAlgebra

open CliffordAlgebra Module Representation

namespace TauCeti

/-- **The central element `ε` acts on an irreducible representation by `±1`**: it is central and
squares to `1`, so it acts by an involutive equivariant endomorphism, which Schur's lemma makes
`±1`. -/
theorem monomialGroup_apply_monomialGroupEpsilon_eq_one_or_eq_neg_one {R M I : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {Q : QuadraticForm R M} (v : I → M) {k : Type*} [Field k]
    {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k (monomialGroup Q v) W)
    [ρ.IsIrreducible] :
    ρ (monomialGroupEpsilon Q v) = 1 ∨ ρ (monomialGroupEpsilon Q v) = -1 := by
  let ε := monomialGroupEpsilon Q v
  have hcentral : ε ∈ Submonoid.center (monomialGroup Q v) := by
    simpa only [← Subgroup.center_toSubmonoid, Subgroup.mem_toSubmonoid] using
      monomialGroupEpsilon_mem_center v
  let T := IntertwiningMap.centralMul ρ ε hcentral
  -- Mathlib exposes no projection lemma for the underlying action of `centralMul`.
  have hTmap : T.toLinearMap = ρ ε := rfl
  have hTapply (w : W) : T w = ρ ε w := rfl
  have hεε : ε * ε = 1 := monomialGroupEpsilon_mul_self v
  have hT : T * T = 1 := by
    apply IntertwiningMap.ext
    simp only [IntertwiningMap.coe_mul, hTmap, ← map_mul, hεε, map_one]
    rfl
  rcases (inferInstance : ρ.IsIrreducible).eq_one_or_eq_neg_one_of_mul_self_eq_one hT with h | h
  · exact Or.inl (LinearMap.ext fun w ↦ by simpa [hTapply, ε] using DFunLike.congr_fun h w)
  · exact Or.inr (LinearMap.ext fun w ↦ by simpa [hTapply, ε] using DFunLike.congr_fun h w)

section Classification

variable {R M I : Type*} [CommRing R] [Nontrivial R] [Invertible (2 : R)] [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M} [LinearOrder I] {b : Basis I R M}
  {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

omit [Nontrivial R] [LinearOrder I] in
/-- In a representation in which `ε` acts by `1`, every signed monomial acts by an operator
commuting with the whole action and squaring to the identity. On an irreducible representation it
therefore acts by `1` or by `-1`. -/
private theorem apply_eq_one_or_eq_neg_one_of_apply_monomialGroupEpsilon_eq_one
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ (monomialGroupEpsilon Q b) = 1) (g : monomialGroup Q b) :
    ρ g = 1 ∨ ρ g = -1 := by
  -- Signed monomials commute up to `ε`, which acts trivially.
  have hcomm (h : monomialGroup Q b) : ρ g * ρ h = ρ h * ρ g := by
    rcases (monomialGroup_commuteOrNeg b
        (fun _ _ hij ↦ QuadraticMap.associated_isOrtho.mp (hb hij)) g h).out with hc | hc
    · have hgh : g * h = h * g := Subtype.ext hc.eq
      rw [← map_mul, hgh, map_mul]
    · have hgh : g * h = monomialGroupEpsilon Q b * (h * g) :=
        Subtype.ext (by simpa using hc.eq)
      rw [← map_mul, hgh, map_mul, hρ, one_mul, map_mul]
  let T : IntertwiningMap ρ ρ := (ρ g).intertwiningMap_of_isIntertwiningMap ρ ρ fun h w ↦ by
    rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]
  -- Every signed monomial squares to `1` or `ε`, which both act trivially.
  have hT : T * T = 1 := DFunLike.ext _ _ fun w ↦ by
    have hsq : ρ g * ρ g = 1 := by
      rw [← map_mul]
      rcases (mem_monomialGroupSign_iff b).mp (mul_self_mem_monomialGroupSign b
          (fun _ _ hij ↦ QuadraticMap.associated_isOrtho.mp (hb hij)) hQ g) with h | h <;>
        simp [h, hρ]
    simpa [T] using DFunLike.congr_fun hsq w
  rcases (inferInstance : ρ.IsIrreducible).eq_one_or_eq_neg_one_of_mul_self_eq_one hT with h | h
  · exact Or.inl (LinearMap.ext fun w ↦ by simpa [T] using DFunLike.congr_fun h w)
  · exact Or.inr (LinearMap.ext fun w ↦ by simpa [T] using DFunLike.congr_fun h w)

omit [Nontrivial R] [LinearOrder I] in
/-- The scalar actions of the signed monomials assemble into a character trivial on `ε`. -/
private theorem exists_character_of_apply_monomialGroupEpsilon_eq_one
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ (monomialGroupEpsilon Q b) = 1) :
    ∃ ψ : monomialGroup Q b →* kˣ, ψ (monomialGroupEpsilon Q b) = 1 ∧
      ∀ g, ρ g = (ψ g : k) • (1 : Module.End k W) := by
  have hirr : ρ.IsIrreducible := inferInstance
  have := hirr.nontrivial
  have hscalar {x y : kˣ} (h : (x : k) • (1 : Module.End k W) = (y : k) • 1) : x = y :=
    Units.ext (smul_left_injective k one_ne_zero h)
  have hsign (g : monomialGroup Q b) : ∃ c : kˣ, ρ g = (c : k) • 1 := by
    rcases apply_eq_one_or_eq_neg_one_of_apply_monomialGroupEpsilon_eq_one hb hQ ρ hρ g with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose c hc using hsign
  let ψ : monomialGroup Q b →* kˣ := .mk' c fun g h ↦ hscalar <| by
    rw [← hc, map_mul, hc, hc, Units.val_mul, mul_smul, smul_one_mul]
  exact ⟨ψ, hscalar (by simp [ψ, ← hc, hρ]), hc⟩

/-- **The irreducible representations in which `ε` acts by `1` are the sign characters.** For an
orthogonal basis indexed by a finite type whose generators square to `±1`, over a field of
characteristic not two, an irreducible representation of the group of signed monomials in which
`ε = -1` acts by `1` is equivalent to the line of the sign character `χ_t : ±e_s ↦ (-1) ^ #(s ∩ t)`
for exactly one index set `t`. -/
theorem monomialGroup_existsUnique_nonempty_equiv_ofLinearCharacter [Finite I] [NeZero (2 : k)]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ (monomialGroupEpsilon Q b) = 1) :
    ∃! t : Finset I, Nonempty (ρ.Equiv (ofLinearCharacter
      ((Units.map (Int.castRingHom k : ℤ →* k)).comp (monomialGroupCharacter hb hQ t)))) := by
  have hirr : ρ.IsIrreducible := inferInstance
  have := hirr.nontrivial
  -- A scalar operator determines its scalar, since `W` is nonzero.
  have hscalar {x y : kˣ} (h : (x : k) • (1 : Module.End k W) = (y : k) • 1) : x = y :=
    Units.ext (smul_left_injective k one_ne_zero h)
  obtain ⟨ψ, hψ, hc⟩ := exists_character_of_apply_monomialGroupEpsilon_eq_one hb hQ ρ hρ
  obtain ⟨t, ht, huniq⟩ := existsUnique_monomialGroupCharacter_eq hb hQ ψ hψ
  refine ⟨t, (hirr.nonempty_equiv_ofLinearCharacter_iff _).mpr fun g ↦ by rw [ht]; exact hc g,
    fun t' ht' ↦ huniq t' (MonoidHom.ext fun g ↦ hscalar ?_)⟩
  rw [← (hirr.nonempty_equiv_ofLinearCharacter_iff _).mp ht' g]
  exact hc g

omit [Nontrivial R] [LinearOrder I] in
/-- **An irreducible representation in which `ε` acts by `1` is a line**, for an orthogonal basis
whose generators square to `±1`, over any field; the basis need not be finite. Unlike
`CliffordAlgebra.finrank_eq_one_of_apply_monomialGroupEpsilon_eq_one`, this needs neither an
algebraically closed field nor a finite-dimensional representation, but it needs the generators to
square to `±1`. -/
theorem monomialGroup_finrank_eq_one_of_apply_monomialGroupEpsilon_eq_one
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ (monomialGroupEpsilon Q b) = 1) :
    finrank k W = 1 := by
  obtain ⟨ψ, -, hψ⟩ := exists_character_of_apply_monomialGroupEpsilon_eq_one hb hQ ρ hρ
  obtain ⟨e⟩ := (inferInstance : ρ.IsIrreducible).nonempty_equiv_ofLinearCharacter_iff ψ |>.mpr hψ
  rw [e.toLinearEquiv.finrank_eq, finrank_self]

end Classification

/-- **In dimension one every irreducible representation is a line.** Over a separably closed field
of characteristic not two, for an orthogonal basis of a line whose generator squares to `±1`, the
group of signed monomials has order four, and each of its irreducible representations is
one-dimensional: those in which `ε` acts by `1` are sign characters, and those in which it acts by
`-1` are spinor representations of dimension `2 ^ 0`. -/
theorem monomialGroup_finrank_eq_one_of_finrank_eq_one {F : Type*} [Field F] [IsSepClosed F]
    [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} {I : Type*} [LinearOrder I] {b : Basis I F V}
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (hV : finrank F V = 1) {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F (monomialGroup Q b) W) [ρ.IsIrreducible] :
    finrank F W = 1 := by
  rcases monomialGroup_apply_monomialGroupEpsilon_eq_one_or_eq_neg_one b ρ with hρ | hρ
  · exact monomialGroup_finrank_eq_one_of_apply_monomialGroupEpsilon_eq_one hb hQ ρ hρ
  · simpa using monomialGroup_finrank_eq_two_pow_of_odd hb hQ (l := 0) (by simpa using hV) ρ hρ

end TauCeti
