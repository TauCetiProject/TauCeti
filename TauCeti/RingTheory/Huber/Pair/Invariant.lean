/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Huber.Subring
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.Topology.Algebra.ConstMulAction
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring

/-!
# The invariant Huber pair of a finite group action

Let a finite group `G` act on a Tate ring `A` by continuous ring automorphisms, and let `(A, A⁺)`
be a Huber pair. The fixed subring `Aᴳ`, with the subspace topology, is again a Tate ring, and
`A^{+G} = A⁺ ∩ Aᴳ` is a ring of integral elements of it, so `(Aᴳ, A^{+G})` is a Huber pair. No
hypothesis is made on the order of `G`: it may be divisible by the residue characteristic, and it
need not be invertible in `A`, so `Aᴳ` is in general not the image of an averaging operator.

The pseudouniformiser of `Aᴳ` is the orbit product `∏ g, g • ϖ` of a pseudouniformiser `ϖ` of
`A`. Since `Aᴳ` contains a pseudouniformiser of `A`, it has the same bounded subsets and the same
power-bounded elements as `A`, so `(Aᴳ)° = A° ∩ Aᴳ`. The ring `A` is integral over `Aᴳ`; when
`G` also preserves `A⁺`, `A⁺` is the integral closure of `A^{+G}` in `A`. If `A` is Hausdorff,
`Aᴳ` is closed in `A`, so it is complete whenever `A` is.

The invariant pair is the base of the quotient `|Spa(A, A⁺)| / G ≅ |Spa(Aᴳ, A^{+G})|` of the adic
spectrum by `G`, and of finite quotients of affinoid perfectoid spaces.

## Main definitions

* `TauCeti.Huber.invariantPair G P`: the Huber pair `(Aᴳ, A⁺ ∩ Aᴳ)`.
* `TauCeti.Huber.invariantPair.map`: the morphism of invariant pairs induced by an equivariant
  morphism of Huber pairs.
* `TauCeti.Huber.invariantPair.subgroup`: the inclusion `(Aᴳ, A^{+G}) → (Aᴴ, A^{+H})` for a
  subgroup `H ≤ G`.

## Main results

* `TauCeti.Huber.IsPseudoUniformizer.orbitProd`: the orbit product of a pseudouniformiser is a
  pseudouniformiser.
* `TauCeti.Huber.IsPseudoUniformizer.orbitProd_fixedPoints`: it is also a pseudouniformiser of
  the fixed subring.
* `TauCeti.Huber.isTateRing_fixedPoints`: `Aᴳ` is a Tate ring, as an instance.
* `TauCeti.Huber.powerBoundedSubring_fixedPoints`: `(Aᴳ)° = A° ∩ Aᴳ`.
* `TauCeti.Huber.integralClosure_map_invariantPair_plus`: if `G` preserves `A⁺`, then `A⁺` is the
  integral closure of `A^{+G}` in `A`.
* The `CompleteSpace` instance on `FixedPoints.subring A G` for a complete Hausdorff ring; its
  uniform additive group structure comes from the general `Subring.isUniformAddGroup`.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021),
  §2 and the proof of Theorem 3.1, Steps 1 and 3: the invariant pseudouniformiser, the
  invariant Tate ring and the integral closure of `A^{+G}`.
-/

public section

open Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] (G : Type*) [Group G] [MulSemiringAction G A]

section Uniform

/-- The fixed subring of a continuous action on a complete Hausdorff ring is complete, being
closed. -/
instance [UniformSpace A] [CompleteSpace A] [T2Space A] [ContinuousConstSMul G A] :
    CompleteSpace (FixedPoints.subring A G) := by
  have h : IsClosed (FixedPoints.subring A G : Set A) := by
    rw [FixedPoints.coe_subring]
    exact isClosed_fixedPoints_of_continuousConstSMul
  exact h.completeSpace_coe

end Uniform

/-- **The orbit product of a pseudouniformiser is a pseudouniformiser.** For a finite group acting
by continuous ring automorphisms, each `g • ϖ` is a pseudouniformiser, and so is their product
`∏ g, g • ϖ`, which is fixed by `G`. -/
theorem IsPseudoUniformizer.orbitProd {R : Type*} [CommSemiring R] [TopologicalSpace R]
    [ContinuousMul R] [MulSemiringAction G R] [Fintype G] [ContinuousConstSMul G R] {ϖ : R}
    (hϖ : IsPseudoUniformizer ϖ) : IsPseudoUniformizer (TauCeti.orbitProd G ϖ) := by
  rw [TauCeti.orbitProd_def]
  exact Finset.prod_induction_nonempty _ IsPseudoUniformizer (fun _ _ ↦ .mul)
    Finset.univ_nonempty fun g _ ↦
      hϖ.map (φ := MulSemiringAction.toRingHom G R g) (continuous_const_smul g)

/-- **The orbit product of a pseudouniformiser is a pseudouniformiser of the fixed subring.** Its
inverse is the orbit product of `ϖ⁻¹`, which is again invariant. -/
theorem IsPseudoUniformizer.orbitProd_fixedPoints [TopologicalSpace A] [ContinuousMul A]
    [Fintype G] [ContinuousConstSMul G A] {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer
      (⟨TauCeti.orbitProd G ϖ, TauCeti.orbitProd_mem_subring G ϖ⟩ : FixedPoints.subring A G) :=
  isPseudoUniformizer_iff.mpr
    ⟨(Units.mkOfMulEqOne _ ⟨_, TauCeti.orbitProd_mem_subring G (↑hϖ.isUnit.unit⁻¹ : A)⟩
      (Subtype.ext (TauCeti.orbitProd_units_mul_inv G hϖ.isUnit.unit))).isUnit,
      isTopologicallyNilpotent_mk _ (hϖ.orbitProd G).isTopologicallyNilpotent⟩

variable [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [Finite G]
  [ContinuousConstSMul G A]

/-- The fixed subring contains a pseudouniformiser of the ambient Tate ring, namely the orbit
product of any pseudouniformiser. -/
theorem exists_isPseudoUniformizer_mem_fixedPoints :
    ∃ ϖ : A, IsPseudoUniformizer ϖ ∧ ϖ ∈ FixedPoints.subring A G := by
  have := Fintype.ofFinite G
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  exact ⟨_, hϖ.orbitProd G, TauCeti.orbitProd_mem_subring G ϖ⟩

/-- **The fixed subring of a finite group acting on a Tate ring is a Tate ring** for the subspace
topology. If `ϖ` is a pseudouniformiser of `A`, its orbit product `N(ϖ) = ∏ g, g • ϖ` is a
pseudouniformiser of `A` and of `Aᴳ` (`IsPseudoUniformizer.orbitProd_fixedPoints`). No hypothesis
is made on the order of `G`. -/
instance isTateRing_fixedPoints : IsTateRing (FixedPoints.subring A G) := by
  have := Fintype.ofFinite G
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  let v := (hϖ.orbitProd_fixedPoints G).isUnit.unit
  exact (FixedPoints.subring A G).isTateRing_of_isPseudoUniformizer
    (Units.map (FixedPoints.subring A G).subtype.toMonoidHom v) (hϖ.orbitProd G)
    (v : FixedPoints.subring A G).property (↑v⁻¹ : FixedPoints.subring A G).property

/-- **Power-bounded invariants** (`(Aᴳ)° = A° ∩ Aᴳ`): an invariant element is power-bounded in
`Aᴳ` exactly when it is power-bounded in `A`. -/
theorem powerBoundedSubring_fixedPoints :
    powerBoundedSubring (FixedPoints.subring A G) =
      (powerBoundedSubring A).comap (FixedPoints.subring A G).subtype :=
  have ⟨_, hϖ, hmem⟩ := exists_isPseudoUniformizer_mem_fixedPoints (A := A) G
  (FixedPoints.subring A G).powerBoundedSubring_eq_comap hϖ hmem

/-- **The invariant Huber pair** `(Aᴳ, A^{+G})` of a finite group acting by continuous ring
automorphisms on a Tate ring, where `A^{+G} = A⁺ ∩ Aᴳ`. Neither the order of `G` nor stability of
`A⁺` under `G` is assumed; only `integralClosure_map_invariantPair_plus` assumes that `G`
preserves `A⁺`. -/
def invariantPair (P : Pair A) : Pair (FixedPoints.subring A G) where
  plus := P.plus.comap (FixedPoints.subring A G).subtype
  isRingOfIntegralElements := P.isRingOfIntegralElements.comap_subtype _

variable {G}

@[simp]
theorem invariantPair_plus (P : Pair A) :
    (invariantPair G P).plus = P.plus.comap (FixedPoints.subring A G).subtype :=
  (rfl)

/-- An invariant element lies in `A^{+G}` exactly when it lies in `A⁺`. -/
theorem mem_invariantPair_plus {P : Pair A} {x : FixedPoints.subring A G} :
    x ∈ (invariantPair G P).plus ↔ (x : A) ∈ P.plus :=
  Iff.rfl

/-- As a subring of `A`, the plus ring of the invariant pair is `A⁺ ∩ Aᴳ`. -/
theorem map_subtype_invariantPair_plus (P : Pair A) :
    (invariantPair G P).plus.map (FixedPoints.subring A G).subtype =
      P.plus ⊓ FixedPoints.subring A G := by
  rw [invariantPair_plus, Subring.map_comap_eq, Subring.range_subtype, inf_comm]

/-- **`A⁺` is the integral closure of `A^{+G}` in `A`** when `G` preserves `A⁺`: every element of
`A⁺` is a root of its orbit polynomial, whose coefficients lie in `A^{+G}`, and `A⁺` is integrally
closed in `A`. -/
theorem integralClosure_map_invariantPair_plus (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) :
    (integralClosure ↥((invariantPair G P).plus.map (FixedPoints.subring A G).subtype)
      A).toSubring = P.plus := by
  have : IsInvariantSubring G P.plus := ⟨fun g _ ha ↦ hP g _ ha⟩
  have := P.isRingOfIntegralElements.isIntegrallyClosedIn
  rw [map_subtype_invariantPair_plus]
  exact P.plus.integralClosure_inf_fixedPoints

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsTateRing B]
  [MulSemiringAction G B] [ContinuousConstSMul G B]

variable (G) in
/-- The morphism of invariant pairs `(Aᴳ, A^{+G}) → (Bᴳ, B^{+G})` induced by a `G`-equivariant
morphism of Huber pairs `(A, A⁺) → (B, B⁺)`: the restriction to invariant elements. -/
def invariantPair.map {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a) :
    (invariantPair G P).Hom (invariantPair G Q) where
  toRingHom := f.toRingHom.restrict _ _ fun a ha g ↦ by rw [← hf, ha g]
  continuous_toRingHom := (f.continuous_toRingHom.comp continuous_subtypeVal).subtype_mk _
  map_mem_plus _ ha := f.map_mem_plus _ ha

/-- After forgetting to `B`, the induced morphism of invariant pairs is the original morphism. -/
@[simp]
theorem invariantPair.coe_map_apply {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a)
    (x : FixedPoints.subring A G) :
    ((invariantPair.map G f hf).toRingHom x : B) = f.toRingHom x :=
  (rfl)

/-- The identity morphism of `(A, A⁺)` induces the identity of `(Aᴳ, A^{+G})`. -/
@[simp]
theorem invariantPair.map_id (P : Pair A) :
    invariantPair.map G (Pair.Hom.id P) (fun _ _ ↦ by simp) = Pair.Hom.id (invariantPair G P) :=
  Pair.Hom.ext (RingHom.ext fun _ ↦ Subtype.ext (by simp))

/-- Restriction to invariants preserves composition. -/
theorem invariantPair.map_comp {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsTateRing C] [MulSemiringAction G C] [ContinuousConstSMul G C] {P : Pair A} {Q : Pair B}
    {S : Pair C} (f' : Q.Hom S) (f : P.Hom Q)
    (hf' : ∀ (g : G) (b : B), f'.toRingHom (g • b) = g • f'.toRingHom b)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a) :
    invariantPair.map G (f'.comp f) (fun g a ↦ by simp [hf, hf']) =
      (invariantPair.map G f' hf').comp (invariantPair.map G f hf) :=
  Pair.Hom.ext (RingHom.ext fun _ ↦ Subtype.ext (by simp))

/-- Restriction to invariants preserves injectivity. -/
theorem invariantPair.map_injective {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a)
    (hinj : Function.Injective f.toRingHom) :
    Function.Injective (invariantPair.map G f hf).toRingHom :=
  fun _ _ h ↦ Subtype.ext (hinj (by simpa using congr_arg Subtype.val h))

end Functoriality

section Subgroup

variable (G) in
/-- For a subgroup `H ≤ G`, the inclusion `(Aᴳ, A^{+G}) → (Aᴴ, A^{+H})` of invariant pairs. -/
def invariantPair.subgroup (H : Subgroup G) (P : Pair A) :
    (invariantPair G P).Hom (invariantPair H P) where
  toRingHom := (FixedPoints.subring A G).subtype.codRestrict (FixedPoints.subring A H)
    fun x h ↦ x.property h
  continuous_toRingHom := continuous_subtypeVal.subtype_mk _
  map_mem_plus _ ha := ha

/-- After forgetting to `A`, the inclusion of invariant pairs is the identity. -/
@[simp]
theorem invariantPair.coe_subgroup_apply (H : Subgroup G) (P : Pair A)
    (x : FixedPoints.subring A G) :
    ((invariantPair.subgroup G H P).toRingHom x : A) = x :=
  (rfl)

/-- The inclusion of invariant pairs for a subgroup is injective. -/
theorem invariantPair.subgroup_injective (H : Subgroup G) (P : Pair A) :
    Function.Injective (invariantPair.subgroup G H P).toRingHom :=
  fun _ _ h ↦ Subtype.ext (by simpa using congr_arg Subtype.val h)

/-- For the whole group, the inclusion of invariant pairs is bijective. -/
theorem invariantPair.subgroup_top_bijective (P : Pair A) :
    Function.Bijective (invariantPair.subgroup G ⊤ P).toRingHom :=
  ⟨invariantPair.subgroup_injective ⊤ P, fun y ↦
    ⟨⟨y, fun g ↦ y.property ⟨g, Subgroup.mem_top g⟩⟩, Subtype.ext (by simp)⟩⟩

end Subgroup

end TauCeti.Huber
