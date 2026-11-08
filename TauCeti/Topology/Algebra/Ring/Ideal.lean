/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The quotient of a topological ring by an ideal

Four things about `R ⧸ I` that its algebraic theory does not record. It is `T1` exactly when
`I` is closed, and hence `T0`; the closure of zero in it is the image of the closure of `I`; and
when `f : R →+* S` presents `S` as a topological quotient of `R`, the
first isomorphism theorem `R ⧸ ker f ≃+* S` is a homeomorphism, so `S` carries the quotient
topology and not merely a coarser one. Finally, the quotient map by a two-sided ideal and the maps
induced out of the quotient are continuous algebra homomorphisms.

Mathlib proves the corresponding statement for the quotient of a topological group by a
subgroup, as `QuotientGroup.t1Space_iff` and `QuotientGroup.instT1Space`. Those are stated for
`G ⧸ N` with `N : AddSubgroup G` in the additive case, whereas `R ⧸ I` is the quotient by an
`Ideal`. The two quotients are definitionally equal — Mathlib's own
`Ideal.topologicalRing_quotient` builds the additive structure of `R ⧸ I` out of
`QuotientAddGroup.instIsTopologicalAddGroup` — but reaching the group statement from an ideal
still means presenting `I` as `I.toAddSubgroup` and transporting the closedness hypothesis along
that presentation, which unification does not do on its own: with only `IsClosed (I : Set R)` in
context, `T1Space (R ⧸ I)` is not synthesized. So the results below are that transport, and
their proofs delegate to Mathlib rather than reproving anything.

Only separate continuity of addition is needed for the separation results, matching the hypotheses
of the group statements they delegate to; no ring topology and no multiplicative continuity is
used. The first isomorphism theorem below asks for even less: only that `R ⧸ ker f` carries the
coinduced topology, which it does by construction.

## The topological first isomorphism theorem

Algebraically, `RingHom.quotientKerEquivOfSurjective` identifies `R ⧸ ker f` with `S` for any
surjective `f`. Topologically that says nothing: `R ⧸ ker f` carries the quotient topology, and a
continuous surjection can land on a strictly coarser topology than the quotient one, so the
bijection is continuous but need not be open. What closes the gap is exactly the hypothesis that
`f` is a *quotient map*, and with it the algebraic isomorphism becomes a homeomorphism.

Over a Tate ring the quotient-map hypothesis is `LinearMap.isQuotientMap_of_isTateRing`, an open
mapping theorem.

Note that closedness of `ker f` comes for free once `S` is `T1`, since a kernel is the preimage of
a point; it is not a further hypothesis of the theorem but a consequence for its consumers, and
`Ideal.Quotient.instT1Space` above then hands back the separation of `R ⧸ ker f`.

## Main results

* `Ideal.Quotient.t1Space_iff`: `T1Space (R ⧸ I) ↔ IsClosed (I : Set R)`.
* `Ideal.Quotient.instT1Space`: the instance form, so that `T0Space (R ⧸ I)` is found
  automatically once `I` is known to be closed.
* `Ideal.Quotient.mk_mem_closure_zero_iff`: the image of `x` in `R ⧸ I` lies in the closure of
  zero exactly when `x` lies in the closure of `I`.
* `Ideal.Quotient.continuous_lift`: a continuous ring homomorphism annihilating a two-sided ideal
  `I` induces a *continuous* homomorphism on `R ⧸ I`, with no hypothesis on `I` beyond
  two-sidedness (in particular, `I` need not be closed).
* `Ideal.Quotient.mkA` and `Ideal.Quotient.liftA`: the quotient map by a two-sided ideal as a
  continuous algebra homomorphism, and the universal property of the quotient for continuous
  algebra homomorphisms; `Ideal.Quotient.continuousAlgHom_ext` says that continuous algebra
  homomorphisms out of `R ⧸ I` are determined by their composites with the quotient map.
* `ContinuousAlgHom.continuous_quotientKerAlgEquivOfSurjective`: the algebraic first isomorphism
  `A ⧸ ker f ≃ B` induced by a continuous surjective algebra homomorphism is continuous.
* `RingHom.isHomeomorph_kerLift`: the map `R ⧸ ker f →+* S` induced by `f` is a homeomorphism when
  `f` is a quotient map. `IsHomeomorph.homeomorph` bundles that as
  `R ⧸ ker f ≃ₜ S`, and the map bundled is the ring homomorphism `RingHom.kerLift`, so the ring
  structure comes along with it and needs no transport of its own.
* `IsOpenQuotientMap.isTopologicalRing`: the target of an open quotient ring homomorphism out of a
  topological ring is a topological ring.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.38, where a rational localisation is
  presented as a quotient `C ⧸ 𝔞` and its Hausdorff completion is taken.
-/

public section

namespace Ideal.Quotient

section Separation

variable {R : Type*} [TopologicalSpace R] [CommRing R] [SeparatelyContinuousAdd R] (I : Ideal R)

/-- The quotient of a topological ring by an ideal is `T1` exactly when the ideal is closed.
This is `QuotientAddGroup.t1Space_iff` read through the identification of `R ⧸ I` with the
quotient of `R` by `I.toAddSubgroup`. -/
theorem t1Space_iff : T1Space (R ⧸ I) ↔ IsClosed (I : Set R) :=
  QuotientAddGroup.t1Space_iff (N := I.toAddSubgroup)

/-- The quotient of a topological ring by a closed ideal is `T1`, hence `T0`. Stated as an
instance, with the closedness of `I` as an instance argument, so that the separation of `R ⧸ I`
is available to instance search wherever `I` is known to be closed; this follows
`Ideal.Quotient.normedCommRing`, which takes `IsClosed (I : Set R)` the same way. -/
instance instT1Space [IsClosed (I : Set R)] : T1Space (R ⧸ I) := (t1Space_iff I).mpr ‹_›

/-- The image of `x` in `R ⧸ I` lies in the closure of zero exactly when `x` lies in the closure
of `I`. -/
@[simp]
theorem mk_mem_closure_zero_iff {x : R} :
    Ideal.Quotient.mk I x ∈ closure ({0} : Set (R ⧸ I)) ↔ x ∈ closure (I : Set R) := by
  -- The quotient map is open and continuous, so preimages commute with closures, and the
  -- preimage of zero is `I`.
  have hopen : IsOpenMap (Ideal.Quotient.mk I) := QuotientAddGroup.isOpenMap_coe
  have hpre : Ideal.Quotient.mk I ⁻¹' ({0} : Set (R ⧸ I)) = (I : Set R) := by
    ext a
    simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [← hpre, ← hopen.preimage_closure_eq_closure_preimage continuous_quotient_mk',
    Set.mem_preimage]

end Separation

/-- **A continuous ring homomorphism that kills a two-sided ideal `I` lifts to a continuous map on
`R ⧸ I`.**

No hypothesis on `I` beyond two-sidedness is needed: closedness of `I` is what makes `R ⧸ I`
separated (`Ideal.Quotient.instT1Space` above), which matters for maps *into* `R ⧸ I`, not for
maps out of it. -/
theorem continuous_lift {R : Type*} [TopologicalSpace R] [Ring R] (I : Ideal R) [I.IsTwoSided]
    {S : Type*} [Semiring S] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) (hI : ∀ a ∈ I, f a = 0) :
    Continuous (Ideal.Quotient.lift I f hI) :=
  -- `R ⧸ I` carries the coinduced topology, so continuity of a map out of it is continuity of its
  -- composite with the quotient map, which is `f`.
  continuous_coinduced_dom.mpr hf

section ContinuousAlgHom

variable (R : Type*) {A B : Type*} [CommSemiring R] [Ring A] [TopologicalSpace A] [Algebra R A]
  (I : Ideal A) [I.IsTwoSided]

/-- The quotient map onto the quotient by a two-sided ideal, as a continuous algebra
homomorphism. -/
noncomputable def mkA : A →A[R] A ⧸ I where
  toAlgHom := Ideal.Quotient.mkₐ R I
  cont := continuous_coinduced_rng

@[simp]
theorem mkA_apply (a : A) : mkA R I a = Ideal.Quotient.mk I a :=
  (rfl)

theorem coe_mkA : ⇑(mkA R I) = Ideal.Quotient.mk I :=
  (rfl)

@[simp]
theorem toAlgHom_mkA : (mkA R I : A →ₐ[R] A ⧸ I) = Ideal.Quotient.mkₐ R I :=
  (rfl)

theorem mkA_surjective : Function.Surjective (mkA R I) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem ker_mkA : RingHom.ker (mkA R I) = I :=
  Ideal.Quotient.mkₐ_ker R I

variable {R} [Semiring B] [TopologicalSpace B] [Algebra R B]

/-- Two continuous algebra homomorphisms out of `A ⧸ I` agree when they agree after composition
with the quotient map. -/
@[ext 1100]
theorem continuousAlgHom_ext {f g : A ⧸ I →A[R] B} (h : f.comp (mkA R I) = g.comp (mkA R I)) :
    f = g :=
  ContinuousAlgHom.coe_inj.mp (Ideal.Quotient.algHom_ext R (congr_arg ContinuousAlgHom.toAlgHom h))

/-- A continuous algebra homomorphism vanishing on a two-sided ideal `I` descends to a continuous
algebra homomorphism on `A ⧸ I`. -/
noncomputable def liftA (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) : A ⧸ I →A[R] B where
  toAlgHom := Ideal.Quotient.liftₐ I f hI
  cont := Ideal.Quotient.continuous_lift I f.continuous hI

@[simp]
theorem toAlgHom_liftA (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) :
    (liftA I f hI : A ⧸ I →ₐ[R] B) = Ideal.Quotient.liftₐ I f hI :=
  (rfl)

@[simp]
theorem liftA_mk (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) (a : A) :
    liftA I f hI (Ideal.Quotient.mk I a) = f a :=
  Ideal.Quotient.lift_mk I (f : A →+* B) hI

@[simp]
theorem liftA_comp_mkA (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) :
    (liftA I f hI).comp (mkA R I) = f :=
  ContinuousAlgHom.ext fun a ↦ liftA_mk I f hI a

end ContinuousAlgHom

end Ideal.Quotient

namespace ContinuousAlgHom

variable {R A B : Type*} [CommSemiring R] [Ring A] [TopologicalSpace A] [Algebra R A]
  [Semiring B] [TopologicalSpace B] [Algebra R B]

/-- The algebraic first isomorphism `A ⧸ ker f ≃ B` induced by a continuous surjective algebra
homomorphism `f` is continuous, being the map `Ideal.Quotient.liftA` induced by `f`. -/
theorem continuous_quotientKerAlgEquivOfSurjective (f : A →A[R] B)
    (hf : Function.Surjective f) :
    Continuous (Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[R] B)) hf) := by
  have h : ⇑(Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[R] B)) hf) =
      ⇑(Ideal.Quotient.liftA (RingHom.ker f) f fun _ ↦ id) := by
    funext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientKerAlgEquivOfSurjective_mk]
    exact (Ideal.Quotient.liftA_mk _ f _ a).symm
  rw [h]
  exact (Ideal.Quotient.liftA (RingHom.ker f) f fun _ ↦ id).continuous

end ContinuousAlgHom

section FirstIsomorphism

open Topology

variable {R S : Type*} [TopologicalSpace R] [CommRing R] [TopologicalSpace S] [Semiring S]
  {f : R →+* S}

namespace RingHom

/-- **The topological first isomorphism theorem for rings.** A ring homomorphism that is a
quotient map presents its target as the quotient of its source by its kernel, topologically as
well as algebraically.

A continuous surjection is not enough on its own. Surjectivity of `f` makes the lift bijective and
continuity of `f` makes it continuous, but a continuous bijection is open only when the topology it
lands in is no coarser than the one it carries; that `f` is a quotient map is exactly the statement
that it is not coarser.

`IsHomeomorph.homeomorph` turns this into `R ⧸ ker f ≃ₜ S`. What it bundles is `RingHom.kerLift`,
which is a ring homomorphism, so a consumer needing the isomorphism of rings has it already —
`RingHom.quotientKerEquivOfSurjective` is that same map. -/
theorem isHomeomorph_kerLift (hq : IsQuotientMap (f : R → S)) : IsHomeomorph (kerLift f) := by
  -- `f` factors as `kerLift f ∘ mk`, and `mk` coinduces, so the quotient-map hypothesis on `f`
  -- transfers to `kerLift f`; an injective quotient map is a homeomorphism
  have hcomp : ⇑(kerLift f) ∘ ⇑(Ideal.Quotient.mk (ker f)) = ⇑f := funext (kerLift_mk f)
  have hmk : IsCoinducing ⇑(Ideal.Quotient.mk (ker f)) := ⟨rfl⟩
  have hkl : IsQuotientMap ⇑(kerLift f) := .of_comp_of_isCoinducing (hcomp ▸ hq) hmk
  exact isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hkl, kerLift_injective f⟩

end RingHom

end FirstIsomorphism

section OpenQuotient

open Topology

/-- **An open quotient of a topological ring is a topological ring.** If `π : R →+* B` is an open
quotient map and `R` is a topological ring, then addition, multiplication and negation on `B` are
continuous, because their composites with the quotient map `π × π` (resp. `π`) are continuous. -/
theorem IsOpenQuotientMap.isTopologicalRing {R B : Type*} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Ring B] [TopologicalSpace B] {π : R →+* B}
    (hπ : IsOpenQuotientMap π) : IsTopologicalRing B := by
  have h2 := hπ.prodMap hπ
  have hadd : Continuous fun p : B × B ↦ p.1 + p.2 := by
    rw [← h2.continuous_comp_iff]
    exact hπ.continuous.comp (continuous_fst.add continuous_snd) |>.congr fun p ↦ by simp
  have hmul : Continuous fun p : B × B ↦ p.1 * p.2 := by
    rw [← h2.continuous_comp_iff]
    exact hπ.continuous.comp (continuous_fst.mul continuous_snd) |>.congr fun p ↦ by simp
  have hneg : Continuous fun b : B ↦ -b := by
    rw [← hπ.continuous_comp_iff]
    exact hπ.continuous.comp continuous_neg |>.congr fun p ↦ by simp
  have : ContinuousAdd B := ⟨hadd⟩
  have : ContinuousMul B := ⟨hmul⟩
  have : ContinuousNeg B := ⟨hneg⟩
  exact {}

end OpenQuotient
