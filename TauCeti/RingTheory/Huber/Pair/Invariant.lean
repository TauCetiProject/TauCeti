/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Huber.Subring
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.Topology.Algebra.Ring.FixedPoints

/-!
# The invariant Huber pair of a finite group action

Let a finite group `G` act on a Tate ring `A` by continuous ring automorphisms. The fixed subring
`Aᴳ = FixedPoints.subring A G`, with the subspace topology, is again a Tate ring: for a
pseudouniformiser `ϖ` of `A`, the orbit product `N(ϖ) = ∏ g : G, g • ϖ` is a `G`-invariant
pseudouniformiser of `A`, and it is a unit of `Aᴳ` because `N(ϖ⁻¹)` is its inverse. If `A` is
complete and Hausdorff, `Aᴳ` is closed, hence complete
(`TauCeti/Topology/Algebra/Ring/FixedPoints.lean`). Its power-bounded elements are those of `A`
lying in `Aᴳ` (`Subring.comap_powerBoundedSubring`).

For a Huber pair `(A, A⁺)`, the trace `A^{+G} = A⁺ ∩ Aᴳ` is a ring of integral elements of `Aᴳ`,
giving the *invariant Huber pair* `(Aᴳ, A^{+G})`. Nothing is assumed about the order of `G`: it
may be divisible by the residue characteristic and need not be invertible in `A`, so no averaging
operator is available, and the fixed ring is not the image of the trace in general. If moreover
`G` maps `A⁺` into itself, then `A⁺` is the integral closure of `A^{+G}` in `A`. The construction
is functorial in equivariant morphisms of Huber pairs, restricts along subgroups, and is the
equalizer of the action: a morphism into `(A, A⁺)` with `G`-invariant values factors uniquely
through the inclusion `(Aᴳ, A^{+G}) → (A, A⁺)`.

The invariant pair is the affinoid input to quotients of adic spaces by finite groups: when `G`
maps `A⁺` into itself, its adic spectrum is the orbit space of `Spa(A, A⁺)`.

## Main definitions

* `TauCeti.Huber.invariantPair G P`: the invariant Huber pair `(Aᴳ, A⁺ ∩ Aᴳ)` of a Huber pair
  `P = (A, A⁺)` on a Tate ring.
* `TauCeti.Huber.invariantPair.inclusion`: the inclusion `(Aᴳ, A^{+G}) → (A, A⁺)`.
* `TauCeti.Huber.invariantPair.lift`: the factorisation through the inclusion of a morphism with
  `G`-invariant values.
* `TauCeti.Huber.invariantPair.map`: the morphism of invariant pairs induced by an equivariant
  morphism of Huber pairs.
* `TauCeti.Huber.invariantPair.subgroup`: the inclusion `(Aᴳ, A^{+G}) → (Aᴴ, A^{+H})` for a
  subgroup `H ≤ G`.

## Main results

* `TauCeti.Huber.IsPseudoUniformizer.orbitProd`: the orbit product of a pseudouniformiser is a
  pseudouniformiser of `A`, and `TauCeti.Huber.IsPseudoUniformizer.orbitProd_mk` one of `Aᴳ`.
* `TauCeti.Huber.isTateRing_fixedPoints`: the fixed subring is a Tate ring (an instance).
* `TauCeti.Huber.Pair.integralClosure_inf_fixedPoints`: for a `G`-stable `A⁺`, the integral
  closure of `A⁺ ∩ Aᴳ` in `A` is `A⁺`.
* `TauCeti.Huber.invariantPair.inclusion_comp_lift` and `TauCeti.Huber.invariantPair.hom_ext`:
  the universal property of the inclusion.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), §2 and
  the proof of Theorem 3.1.
-/

public section

open TauCeti.MulDistribMulAction

namespace TauCeti.Huber

/-- **The orbit product of a pseudouniformiser is a pseudouniformiser**, for a finite group
acting by continuous multiplicative automorphisms on a commutative topological monoid with zero
and continuous multiplication. -/
theorem IsPseudoUniformizer.orbitProd {A : Type*} [CommMonoidWithZero A] (G : Type*) [Group G]
    [Finite G] [MulDistribMulAction G A] [TopologicalSpace A] [ContinuousMul A]
    [ContinuousConstSMul G A] {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer (MulDistribMulAction.orbitProd G ϖ) := by
  cases nonempty_fintype G
  rw [orbitProd_eq_prod]
  refine IsPseudoUniformizer.prod Finset.univ_nonempty fun g _ ↦ ?_
  -- `g • ·` is a continuous monoid-with-zero endomorphism.
  let φ : A →*₀ A := { MulDistribMulAction.toMonoidHom A g with map_zero' := by simp }
  exact hϖ.map (φ := φ) (continuous_const_smul g)

variable {A : Type*} [CommRing A] (G : Type*) [Group G] [MulSemiringAction G A]

variable {G} in
/-- **`A⁺` is the integral closure of `A^{+G}`.** If a finite group `G` maps the ring of integral
elements `A⁺` of a Huber pair into itself, the integral closure of `A⁺ ∩ Aᴳ` in `A` is `A⁺`. No
continuity of the action is needed. -/
theorem Pair.integralClosure_inf_fixedPoints [Finite G] [TopologicalSpace A] [IsTopologicalRing A]
    [IsHuberRing A] (P : Pair A) (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) :
    (integralClosure ↥(P.plus ⊓ FixedPoints.subring A G) A).toSubring = P.plus :=
  have := P.isRingOfIntegralElements.isIntegrallyClosedIn
  P.plus.integralClosure_inf_fixedPoints hP

section Tate

variable [Finite G] [TopologicalSpace A] [ContinuousConstSMul G A]

/-- **The orbit product of a pseudouniformiser is a pseudouniformiser of the fixed subring**,
for its subspace topology. -/
theorem IsPseudoUniformizer.orbitProd_mk [ContinuousMul A] {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer
      (⟨MulDistribMulAction.orbitProd G ϖ, orbitProd_mem_fixedPoints G ϖ⟩ :
        FixedPoints.subring A G) := by
  obtain ⟨u, rfl⟩ := hϖ.isUnit
  exact isPseudoUniformizer_iff.mpr
    ⟨IsUnit.of_mul_eq_one ⟨_, orbitProd_mem_fixedPoints G (↑u⁻¹ : A)⟩
      (Subtype.ext (orbitProd_mul_orbitProd_inv G u)),
      isTopologicallyNilpotent_mk _ (hϖ.orbitProd G).isTopologicallyNilpotent⟩

/-- **The fixed subring of a finite group acting continuously on a Tate ring is a Tate ring**
for the subspace topology. The order of the group is arbitrary. -/
instance isTateRing_fixedPoints [IsTopologicalRing A] [IsTateRing A] :
    IsTateRing (FixedPoints.subring A G) := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨u, rfl⟩ := hϖ.isUnit
  exact Subring.isTateRing_of_isPseudoUniformizer _
    (Units.mkOfMulEqOne _ _ (orbitProd_mul_orbitProd_inv G u)) (hϖ.orbitProd G)
    (orbitProd_mem_fixedPoints G _) (orbitProd_mem_fixedPoints G _)

end Tate

section Pair

variable [Finite G] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [ContinuousConstSMul G A]

/-- **The invariant Huber pair** `(Aᴳ, A^{+G})` of a Huber pair `(A, A⁺)` on a Tate ring with a
finite group acting by continuous ring automorphisms: `Aᴳ` is the fixed subring with its subspace
topology and `A^{+G} = A⁺ ∩ Aᴳ`. No hypothesis on the order of `G` is made, and the definition
does not need `G` to map `A⁺` into itself. Results comparing the pair with `(A, A⁺)` beyond the
inclusion, such as the description of `A⁺` as the integral closure of `A^{+G}`
(`TauCeti.Huber.Pair.integralClosure_inf_fixedPoints`), do need it. -/
def invariantPair (P : Pair A) : Pair (FixedPoints.subring A G) where
  plus := P.plus.comap (FixedPoints.subring A G).subtype
  isRingOfIntegralElements := P.isRingOfIntegralElements.comap_subtype _

variable {G}

theorem invariantPair_plus (P : Pair A) :
    (invariantPair G P).plus = P.plus.comap (FixedPoints.subring A G).subtype :=
  (rfl)

/-- An invariant element lies in `A^{+G}` exactly when it lies in `A⁺`. -/
@[simp]
theorem mem_invariantPair_plus {P : Pair A} {x : FixedPoints.subring A G} :
    x ∈ (invariantPair G P).plus ↔ (x : A) ∈ P.plus :=
  Iff.rfl

/-- The image of `A^{+G}` in `A` is `A⁺ ∩ Aᴳ`. -/
@[simp]
theorem map_subtype_invariantPair_plus (P : Pair A) :
    (invariantPair G P).plus.map (FixedPoints.subring A G).subtype =
      P.plus ⊓ FixedPoints.subring A G := by
  rw [invariantPair_plus, Subring.map_comap_eq, Subring.range_subtype]

section Inclusion

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

variable (G) in
/-- The inclusion `(Aᴳ, A^{+G}) → (A, A⁺)` of the invariant Huber pair. -/
def invariantPair.inclusion (P : Pair A) : (invariantPair G P).Hom P where
  toRingHom := (FixedPoints.subring A G).subtype
  continuous_toRingHom := continuous_subtype_val
  map_mem_plus _ ha := ha

@[simp]
theorem invariantPair.toRingHom_inclusion (P : Pair A) :
    (invariantPair.inclusion G P).toRingHom = (FixedPoints.subring A G).subtype :=
  (rfl)

/-- **The universal property of the invariant pair.** A morphism of Huber pairs into `(A, A⁺)`
whose values are fixed by `G` factors through the inclusion `(Aᴳ, A^{+G}) → (A, A⁺)`. -/
def invariantPair.lift {P : Pair A} {Q : Pair B} (f : Q.Hom P)
    (hf : ∀ (g : G) (b : B), g • f.toRingHom b = f.toRingHom b) :
    Q.Hom (invariantPair G P) where
  toRingHom := f.toRingHom.codRestrict _ fun b ↦ FixedPoints.mem_subring.mpr fun g ↦ hf g b
  continuous_toRingHom := f.continuous_toRingHom.subtype_mk _
  map_mem_plus _ hb := f.map_mem_plus _ hb

@[simp]
theorem invariantPair.coe_lift_toRingHom_apply {P : Pair A} {Q : Pair B} (f : Q.Hom P)
    (hf : ∀ (g : G) (b : B), g • f.toRingHom b = f.toRingHom b) (b : B) :
    ((invariantPair.lift f hf).toRingHom b : A) = f.toRingHom b :=
  (rfl)

@[simp]
theorem invariantPair.inclusion_comp_lift {P : Pair A} {Q : Pair B} (f : Q.Hom P)
    (hf : ∀ (g : G) (b : B), g • f.toRingHom b = f.toRingHom b) :
    (invariantPair.inclusion G P).comp (invariantPair.lift f hf) = f := by
  ext
  simp

/-- Morphisms into the invariant pair are determined by their composite with the inclusion. -/
theorem invariantPair.hom_ext {P : Pair A} {Q : Pair B} {f f' : Q.Hom (invariantPair G P)}
    (h : (invariantPair.inclusion G P).comp f = (invariantPair.inclusion G P).comp f') :
    f = f' :=
  Pair.Hom.ext <| RingHom.ext fun b ↦ Subtype.ext <| by
    simpa using congr(Pair.Hom.toRingHom $h b)

end Inclusion

section Map

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsTateRing B]
  [MulSemiringAction G B] [ContinuousConstSMul G B]

/-- The morphism of invariant Huber pairs induced by a `G`-equivariant morphism of Huber pairs:
the restriction of the underlying ring map to the fixed subrings. -/
def invariantPair.map {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a) :
    (invariantPair G P).Hom (invariantPair G Q) where
  toRingHom := f.toRingHom.restrict _ _ fun a ha ↦ FixedPoints.mem_subring.mpr fun g ↦ by
    rw [← hf, FixedPoints.mem_subring.mp ha g]
  continuous_toRingHom := (f.continuous_toRingHom.comp continuous_subtype_val).subtype_mk _
  map_mem_plus _ ha := f.map_mem_plus _ ha

@[simp]
theorem invariantPair.coe_map_toRingHom_apply {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a)
    (x : FixedPoints.subring A G) :
    ((invariantPair.map f hf).toRingHom x : B) = f.toRingHom x :=
  (rfl)

/-- The induced morphism of invariant pairs is compatible with the inclusions. -/
@[simp]
theorem invariantPair.inclusion_comp_map {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a) :
    (invariantPair.inclusion G Q).comp (invariantPair.map f hf) =
      f.comp (invariantPair.inclusion G P) := by
  ext
  simp

@[simp]
theorem invariantPair.map_id (P : Pair A) :
    invariantPair.map (Pair.Hom.id P) (fun _ _ ↦ by simp) = Pair.Hom.id (invariantPair G P) := by
  ext
  simp

theorem invariantPair.map_comp {C : Type*} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsTateRing C] [MulSemiringAction G C] [ContinuousConstSMul G C]
    {P : Pair A} {Q : Pair B} {R : Pair C} (f : P.Hom Q) (f' : Q.Hom R)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a)
    (hf' : ∀ (g : G) (b : B), f'.toRingHom (g • b) = g • f'.toRingHom b) :
    invariantPair.map (f'.comp f) (fun g a ↦ by simp [hf, hf']) =
      (invariantPair.map f' hf').comp (invariantPair.map f hf) := by
  ext
  simp

/-- An injective equivariant morphism of Huber pairs induces a morphism of invariant pairs with
injective underlying ring map. -/
theorem invariantPair.map_toRingHom_injective {P : Pair A} {Q : Pair B} (f : P.Hom Q)
    (hf : ∀ (g : G) (a : A), f.toRingHom (g • a) = g • f.toRingHom a)
    (hinj : Function.Injective f.toRingHom) :
    Function.Injective (invariantPair.map f hf).toRingHom := fun _ _ h ↦
  Subtype.ext (hinj congr(Subtype.val $h))

end Map

section Subgroup

variable (H : Subgroup G)

/-- For a subgroup `H ≤ G`, the inclusion of invariant Huber pairs
`(Aᴳ, A^{+G}) → (Aᴴ, A^{+H})`. -/
def invariantPair.subgroup (P : Pair A) : (invariantPair G P).Hom (invariantPair H P) where
  toRingHom := Subring.inclusion fun _ ha ↦ FixedPoints.mem_subring.mpr fun h ↦
    FixedPoints.mem_subring.mp ha h
  continuous_toRingHom := continuous_subtype_val.subtype_mk _
  map_mem_plus _ ha := ha

@[simp]
theorem invariantPair.coe_subgroup_toRingHom_apply (P : Pair A) (x : FixedPoints.subring A G) :
    ((invariantPair.subgroup H P).toRingHom x : A) = x :=
  (rfl)

/-- Restriction to a subgroup is compatible with the inclusions into `(A, A⁺)`. -/
@[simp]
theorem invariantPair.inclusion_comp_subgroup (P : Pair A) :
    (invariantPair.inclusion H P).comp (invariantPair.subgroup H P) =
      invariantPair.inclusion G P := by
  ext
  simp

/-- Restriction of invariants to a subgroup has injective underlying ring map. -/
theorem invariantPair.subgroup_toRingHom_injective (P : Pair A) :
    Function.Injective (invariantPair.subgroup H P).toRingHom := fun _ _ h ↦
  Subtype.ext congr(Subtype.val $h)

/-- Restriction to the whole group has bijective underlying ring map. -/
theorem invariantPair.subgroup_top_toRingHom_bijective (P : Pair A) :
    Function.Bijective (invariantPair.subgroup (⊤ : Subgroup G) P).toRingHom :=
  ⟨invariantPair.subgroup_toRingHom_injective _ P, fun x ↦
    ⟨⟨x, FixedPoints.mem_subring.mpr fun g ↦ FixedPoints.mem_subring.mp x.2 ⟨g, trivial⟩⟩, rfl⟩⟩

end Subgroup

end Pair

end TauCeti.Huber
