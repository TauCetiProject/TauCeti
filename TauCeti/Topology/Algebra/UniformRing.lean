/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Completions of uniform topological rings

Results about `UniformSpace.Completion` as a ring: extensionality for continuous ring
homomorphisms, comparison across equal uniformities, and the identification of a complete
Hausdorff ring with its completion.

`UniformSpace.Completion.ringHom_ext_of_continuous` is `UniformSpace.Completion.ext` for ring
homomorphisms: two continuous ring homomorphisms out of `Completion R` that agree after composing
with the coercion from `R` are equal. `R` is a topological ring carrying a compatible uniform
additive-group structure, and nothing more: neither `CompleteSpace` nor `T0Space` is required, and
`R` need not be commutative. This extensionality principle lets consumers state uniqueness on
the base ring instead of on the completion.

## The completion of a complete separated ring is itself

`UniformSpace.Completion.completeRingEquivSelf`: for a complete Hausdorff topological ring
`S`, the extension of the identity is a ring isomorphism `UniformSpace.Completion S ≃+* S`.
Its underlying function is that of the uniform bijection `UniformCompletion.completeEquivSelf`,
and its inverse is the canonical map from `S` into its completion.

The rest of the self-equivalence material is read off that identification. The isomorphism
is uniformly continuous
because `UniformCompletion.completeEquivSelf` is a uniform equivalence, and its inverse is
uniformly continuous because it *is* the canonical map into the completion. Over a base ring
`R` acting by *uniformly continuous* scalar multiplication the same map is `R`-linear, giving
`UniformSpace.Completion.completeAlgEquivSelf`. Uniform continuity of the action is not a
convenience: it is what makes the completion an `R`-algebra in the first place, since that is
what `UniformSpace.Completion.algebra` requires.

## Comparison across equal uniformities

`RingHom.completionCoe_comp_heq` compares the coercion for two *equal* uniformities on the same
ring: following a fixed map by the coercion gives heterogeneously equal composites. It uses `HEq`
because the completion types depend on their uniformities.

`TauCeti.completionRingHom_heq_of_uniformSpace_eq` transports the characterization of a continuous
ring homomorphism between completions across equal source and target uniformities. The completed
rings may be noncommutative, and the fixed source of their structure maps may be a nonassociative
semiring. `TauCeti.ringHom_flat_of_completion_heq` transports flatness across such a heterogeneous
equality of maps, and `TauCeti.ringHom_flat_of_heq_of_uniformSpace_eq` gives the same transport for
maps from a fixed commutative ring into completions.

## Main definitions

* `UniformSpace.Completion.completeRingEquivSelf`: the ring isomorphism
  `UniformSpace.Completion S ≃+* S`.
* `UniformSpace.Completion.completeAlgEquivSelf`: the same map as an `R`-algebra equivalence,
  for a complete Hausdorff topological `R`-algebra `S` whose scalar multiplication by `R` is
  uniformly continuous (`UniformContinuousConstSMul R S`).

## Main results

* `RingHom.completionCoe_comp_heq`: equal uniformities on the codomain give heterogeneously equal
  composites with the coercion into the completion.
* `TauCeti.completionRingHom_heq_of_uniformSpace_eq`: compares continuous ring homomorphisms
  between completions for equal source and target uniformities.
* `TauCeti.ringHom_flat_of_completion_heq` and
  `TauCeti.ringHom_flat_of_heq_of_uniformSpace_eq`: transport flatness across heterogeneous map
  equalities between completions, or from a fixed ring into completions.
* `UniformSpace.Completion.ringHom_ext_of_continuous`: two continuous ring homomorphisms out of
  a completion that agree on the image of the coercion are equal.
* `UniformSpace.Completion.continuous_mapRingEquiv` and
  `UniformSpace.Completion.continuous_mapRingEquiv_symm`: the isomorphism of completions induced
  by a topological ring isomorphism is continuous in both directions.
* `UniformSpace.Completion.coe_completeRingEquivSelf` and
  `UniformSpace.Completion.coe_completeRingEquivSelf_symm`: the isomorphism is
  `UniformCompletion.completeEquivSelf` and its inverse is the coercion into the completion.
* `UniformSpace.Completion.uniformContinuous_completeRingEquivSelf` and
  `UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm`: both directions are
  uniformly continuous, hence continuous by `UniformContinuous.continuous`.
-/

public section

namespace UniformSpace.Completion

section Congr

/-- **Following a fixed map by the coercion into a completion depends on the uniformity only
through the instance.** For two equal uniformities on `S`, the composites
`R →+* S → UniformSpace.Completion S` agree.

The conclusion is `HEq` rather than `=` because the type `UniformSpace.Completion S` mentions the
uniformity on `S`, so the two composites do not share a codomain. A caller holding an equation
between uniformities — rather than a defeq — is the intended consumer. -/
theorem _root_.RingHom.completionCoe_comp_heq {R S : Type*} [NonAssocSemiring R] [Ring S]
    (f : R →+* S)
    {u₁ u₂ : UniformSpace S} (hu : u₁ = u₂)
    (t₁ : @IsTopologicalRing S u₁.toTopologicalSpace _)
    (t₂ : @IsTopologicalRing S u₂.toTopologicalSpace _)
    (g₁ : @IsUniformAddGroup S u₁ _) (g₂ : @IsUniformAddGroup S u₂ _) :
    HEq ((@coeRingHom S _ u₁ t₁ g₁).comp f) ((@coeRingHom S _ u₂ t₂ g₂).comp f) := by
  subst hu
  rfl

end Congr

section Ext

variable {R : Type*} [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R]
  {B : Type*} [NonAssocSemiring B] [TopologicalSpace B] [T2Space B]

/-- **Maps out of a completion are determined on the image of the coercion.** Two continuous
ring homomorphisms `R̂ → B` into a non-associative semiring carrying a Hausdorff topology that
agree after composing with `coeRingHom` are equal.

This is `UniformSpace.Completion.ext` packaged for ring homomorphisms: composing with `coeRingHom`
is restriction along the coercion, and density of the image does the rest. Nothing is asked of `B`
beyond a non-associative semiring structure and a Hausdorff topology — no compatibility between the
two is used — and `R` need not be commutative. -/
theorem ringHom_ext_of_continuous {g h : Completion R →+* B} (hg : Continuous g)
    (hh : Continuous h) (hcomp : g.comp coeRingHom = h.comp coeRingHom) : g = h :=
  DFunLike.ext' (ext hg hh fun x ↦ congrArg (fun k : R →+* B ↦ k x) hcomp)

end Ext

section MapRingEquiv

variable {α β : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  [Ring β] [UniformSpace β] [IsTopologicalRing β] [IsUniformAddGroup β]

/-- The ring isomorphism of completions induced by a topological ring isomorphism is continuous:
its underlying map is `UniformSpace.Completion.map`. -/
theorem continuous_mapRingEquiv (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm) :
    Continuous (mapRingEquiv f hf hf') :=
  continuous_map.congr fun x ↦ (mapRingEquiv_apply f hf hf' x).symm

/-- The inverse of the ring isomorphism of completions induced by a topological ring isomorphism
is continuous. -/
theorem continuous_mapRingEquiv_symm (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm) :
    Continuous (mapRingEquiv f hf hf').symm :=
  continuous_map.congr fun x ↦ (mapRingEquiv_symm_apply f hf hf' x).symm

end MapRingEquiv

variable (S : Type*) [Ring S] [UniformSpace S] [IsTopologicalRing S] [IsUniformAddGroup S]
  [CompleteSpace S] [T0Space S]

/-- The extension of the identity ring homomorphism and the uniform bijection
`UniformCompletion.completeEquivSelf` are the same function: both are
`UniformSpace.Completion.extension id`. -/
private theorem coe_extensionHom_id :
    ⇑(extensionHom (RingHom.id S) continuous_id) =
      ⇑(UniformCompletion.completeEquivSelf (α := S)) := (rfl)

/-- For a complete Hausdorff topological ring, the extension of the identity is a ring
isomorphism from the completion. -/
noncomputable def completeRingEquivSelf : UniformSpace.Completion S ≃+* S :=
  RingEquiv.ofBijective (extensionHom (RingHom.id S) continuous_id)
    (coe_extensionHom_id S ▸ (UniformCompletion.completeEquivSelf (α := S)).bijective)

/-- The isomorphism undoes the canonical inclusion: on an element of `S` regarded as an
element of the completion, it returns that element. -/
@[simp]
theorem completeRingEquivSelf_coe (a : S) :
    completeRingEquivSelf S (a : UniformSpace.Completion S) = a :=
  extensionHom_coe (RingHom.id S) continuous_id a

/-- The inverse isomorphism **is** the canonical inclusion: it sends an element of `S` to
itself, regarded as an element of the completion. -/
@[simp]
theorem completeRingEquivSelf_symm_apply (a : S) :
    (completeRingEquivSelf S).symm a = (a : UniformSpace.Completion S) :=
  (RingEquiv.symm_apply_eq _).mpr (completeRingEquivSelf_coe S a).symm

/-- The isomorphism **is** the uniform bijection `UniformCompletion.completeEquivSelf`, as a
function: both are `UniformSpace.Completion.extension id`. -/
theorem coe_completeRingEquivSelf :
    ⇑(completeRingEquivSelf S) = ⇑(UniformCompletion.completeEquivSelf (α := S)) :=
  coe_extensionHom_id S

/-- The inverse isomorphism **is** the canonical map into the completion, as a function. -/
theorem coe_completeRingEquivSelf_symm :
    ⇑(completeRingEquivSelf S).symm = ((↑) : S → UniformSpace.Completion S) :=
  funext (completeRingEquivSelf_symm_apply S)

/-- The isomorphism is uniformly continuous: it is the uniform bijection
`UniformCompletion.completeEquivSelf`. -/
theorem uniformContinuous_completeRingEquivSelf :
    UniformContinuous ⇑(completeRingEquivSelf S) :=
  coe_completeRingEquivSelf S ▸ (UniformCompletion.completeEquivSelf (α := S)).uniformContinuous

/-- The inverse isomorphism is uniformly continuous: it is the canonical map into the
completion. -/
theorem uniformContinuous_completeRingEquivSelf_symm :
    UniformContinuous ⇑(completeRingEquivSelf S).symm :=
  coe_completeRingEquivSelf_symm S ▸ uniformContinuous_coe S

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R S] [UniformContinuousConstSMul R S]

/-- For a complete Hausdorff topological `R`-algebra `S` whose scalar multiplication by `R` is
uniformly continuous (`UniformContinuousConstSMul R S`, which is what gives the completion its
`R`-algebra structure), the extension of the identity is an `R`-algebra equivalence from the
completion: `completeRingEquivSelf` is `R`-linear, since it fixes the image of `R`. -/
noncomputable def completeAlgEquivSelf : UniformSpace.Completion S ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := completeRingEquivSelf S) fun r ↦ by
    rw [algebraMap_def]
    exact completeRingEquivSelf_coe S _

/-- The algebra equivalence has the same underlying map as the ring isomorphism, so `simp`
normalises the `R`-algebra bundling onto the ring one. -/
@[simp]
theorem coe_completeAlgEquivSelf :
    ⇑(completeAlgEquivSelf S R) = ⇑(completeRingEquivSelf S) := (rfl)

/-- The inverses agree too, so the two bundlings normalise together in both directions. -/
@[simp]
theorem coe_completeAlgEquivSelf_symm :
    ⇑(completeAlgEquivSelf S R).symm = ⇑(completeRingEquivSelf S).symm := (rfl)

end Algebra

end UniformSpace.Completion

namespace TauCeti

/-- Two completion ring homomorphisms are heterogeneously equal when their source and target
uniformities agree and the first map satisfies the characterization that uniquely determines the
second. The rings being completed need not be commutative, and the fixed source of the structure
maps need only be a nonassociative semiring. -/
theorem completionRingHom_heq_of_uniformSpace_eq
    {A S S' : Type*} [NonAssocSemiring A] [Ring S] [Ring S']
    {u₁ u₂ : UniformSpace S} (hu : u₂ = u₁) {v₁ v₂ : UniformSpace S'} (hv : v₂ = v₁)
    (g₁ : @IsUniformAddGroup S u₁ _) (g₂ : @IsUniformAddGroup S u₂ _)
    (t₁ : @IsTopologicalRing S u₁.toTopologicalSpace _)
    (t₂ : @IsTopologicalRing S u₂.toTopologicalSpace _)
    (g₁' : @IsUniformAddGroup S' v₁ _) (g₂' : @IsUniformAddGroup S' v₂ _)
    (t₁' : @IsTopologicalRing S' v₁.toTopologicalSpace _)
    (t₂' : @IsTopologicalRing S' v₂.toTopologicalSpace _) :
    let B₁ := @UniformSpace.Completion S u₁
    let B₂ := @UniformSpace.Completion S u₂
    let C₁ := @UniformSpace.Completion S' v₁
    let C₂ := @UniformSpace.Completion S' v₂
    let b₁ := @UniformSpace.Completion.ring S _ u₁ t₁ g₁
    let b₂ := @UniformSpace.Completion.ring S _ u₂ t₂ g₂
    let c₁ := @UniformSpace.Completion.ring S' _ v₁ t₁' g₁'
    let c₂ := @UniformSpace.Completion.ring S' _ v₂ t₂' g₂'
    ∀ (f₂ : @RingHom B₂ C₂ b₂.toNonAssocSemiring c₂.toNonAssocSemiring)
      (f₁ : @RingHom B₁ C₁ b₁.toNonAssocSemiring c₁.toNonAssocSemiring)
      (a₂ : @RingHom A B₂ _ b₂.toNonAssocSemiring)
      (a₁ : @RingHom A B₁ _ b₁.toNonAssocSemiring)
      (d₂ : @RingHom A C₂ _ c₂.toNonAssocSemiring)
      (d₁ : @RingHom A C₁ _ c₁.toNonAssocSemiring),
      @Continuous B₂ C₂ (@UniformSpace.Completion.uniformSpace S u₂).toTopologicalSpace
        (@UniformSpace.Completion.uniformSpace S' v₂).toTopologicalSpace f₂ →
      HEq a₂ a₁ → HEq d₂ d₁ → f₂.comp a₂ = d₂ →
      (∀ f : @RingHom B₁ C₁ b₁.toNonAssocSemiring c₁.toNonAssocSemiring,
        @Continuous B₁ C₁
          (@UniformSpace.Completion.uniformSpace S u₁).toTopologicalSpace
          (@UniformSpace.Completion.uniformSpace S' v₁).toTopologicalSpace f →
        f.comp a₁ = d₁ → f = f₁) →
      HEq f₂ f₁ := by
  subst hu
  subst hv
  dsimp only
  intro f₂ f₁ a₂ a₁ d₂ d₁ hf₂ ha hd hcomp₂ huniq
  apply heq_of_eq
  apply huniq f₂ hf₂
  rw [← eq_of_heq ha, hcomp₂, eq_of_heq hd]

/-- Flatness passes across a heterogeneous equality between ring homomorphisms of completions
whose source and target uniformities agree. -/
theorem ringHom_flat_of_completion_heq
    {S S' : Type*} [CommRing S] [CommRing S']
    {u₁ u₂ : UniformSpace S} (hu : u₂ = u₁) {v₁ v₂ : UniformSpace S'} (hv : v₂ = v₁)
    (g₁ : @IsUniformAddGroup S u₁ _) (g₂ : @IsUniformAddGroup S u₂ _)
    (t₁ : @IsTopologicalRing S u₁.toTopologicalSpace _)
    (t₂ : @IsTopologicalRing S u₂.toTopologicalSpace _)
    (g₁' : @IsUniformAddGroup S' v₁ _) (g₂' : @IsUniformAddGroup S' v₂ _)
    (t₁' : @IsTopologicalRing S' v₁.toTopologicalSpace _)
    (t₂' : @IsTopologicalRing S' v₂.toTopologicalSpace _) :
    let R₁ := @UniformSpace.Completion S u₁
    let R₂ := @UniformSpace.Completion S u₂
    let B₁ := @UniformSpace.Completion S' v₁
    let B₂ := @UniformSpace.Completion S' v₂
    let r₁ := @UniformSpace.Completion.commRing S _ u₁ g₁ t₁
    let r₂ := @UniformSpace.Completion.commRing S _ u₂ g₂ t₂
    let b₁ := @UniformSpace.Completion.commRing S' _ v₁ g₁' t₁'
    let b₂ := @UniformSpace.Completion.commRing S' _ v₂ g₂' t₂'
    ∀ (f₂ : @RingHom R₂ B₂ r₂.toNonAssocSemiring b₂.toNonAssocSemiring)
      (f₁ : @RingHom R₁ B₁ r₁.toNonAssocSemiring b₁.toNonAssocSemiring),
      HEq f₂ f₁ → @RingHom.Flat R₂ B₂ r₂ b₂ f₂ →
        @RingHom.Flat R₁ B₁ r₁ b₁ f₁ := by
  subst hu
  subst hv
  -- With both uniformities identified, the completion ring structures also agree.
  exact fun _ _ hf hflat ↦ hf.eq ▸ hflat

/-- Flatness of a ring homomorphism from `A` into a completion passes across a heterogeneous
equality with a ring homomorphism into the completion for an equal uniformity. This is the
fixed-source form of `TauCeti.ringHom_flat_of_completion_heq`: `A` keeps its ring structure, and
only the uniformity of `S`, hence its completion, varies. For instance, it compares the canonical
maps from `A` into two completions of a localisation `S` whose uniformities agree. -/
theorem ringHom_flat_of_heq_of_uniformSpace_eq {A S : Type*} [CommRing A] [CommRing S]
    {u₁ u₂ : UniformSpace S} (hu : u₂ = u₁) (g₁ : @IsUniformAddGroup S u₁ _)
    (g₂ : @IsUniformAddGroup S u₂ _) (t₁ : @IsTopologicalRing S u₁.toTopologicalSpace _)
    (t₂ : @IsTopologicalRing S u₂.toTopologicalSpace _) :
    let B₁ := @UniformSpace.Completion S u₁
    let B₂ := @UniformSpace.Completion S u₂
    let b₁ := @UniformSpace.Completion.commRing S _ u₁ g₁ t₁
    let b₂ := @UniformSpace.Completion.commRing S _ u₂ g₂ t₂
    ∀ (f₂ : @RingHom A B₂ _ b₂.toNonAssocSemiring) (f₁ : @RingHom A B₁ _ b₁.toNonAssocSemiring),
      HEq f₂ f₁ → @RingHom.Flat A B₂ _ b₂ f₂ → @RingHom.Flat A B₁ _ b₁ f₁ := by
  subst hu
  -- with the uniformities identified, both completions carry the same ring structure
  exact fun _ _ hf hflat ↦ hf.eq ▸ hflat

end TauCeti
