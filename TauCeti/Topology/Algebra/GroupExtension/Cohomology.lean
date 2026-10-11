/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.Topology.Algebra.GroupExtension.Profinite

/-!
# Continuous `H²` classifies profinite extensions

Let `G` be a topological group acting continuously on a commutative topological group `M`. A
continuous factor set `α : FactorSet G M` — a normalized multiplicative `2`-cocycle that is
continuous as a function on `G × G` — is a continuous `2`-cocycle of the explicit complex of
continuous cochains once it is read additively, so it has a class in the explicit continuous
cohomology group `H²(G, M) = Z²/B²` of `TauCeti.ContCohomology.H2`. This file builds that class and
proves that it is a complete invariant of `α` modulo *continuous* coboundaries: two continuous
factor sets have the same class exactly when their quotient is the coboundary of a continuous
function (`TauCeti.FactorSet.contCohomologyClass_eq_iff`), and every class is the class of a
continuous factor set (`TauCeti.FactorSet.exists_contCohomologyClass_eq`). So the class descends
to a bijection `TauCeti.FactorSet.contCohomologyClassEquiv` from the continuous factor sets modulo
continuous cohomology onto `H²(G, M)`.

Read through the extension dictionary, this classifies extensions of topological groups. Consider
an extension `1 → M → E → G → 1` of topological groups inducing the given action of `G` on `M`,
whose kernel is embedded (`S.inl` is an embedding) and which has a continuous normalized section.
It has a class, that of the factor set of the section, which does not depend on the section
(`TauCeti.GroupExtension.contCohomologyClass_factorSet_eq`); two such extensions, both with
continuous projection, are equivalent by a continuous equivalence exactly when their classes agree
(`TauCeti.GroupExtension.exists_equiv_continuous_iff_contCohomologyClass_factorSet_eq`), and equal
classes even yield a homeomorphic equivalence
(`TauCeti.GroupExtension.exists_equiv_isHomeomorph_of_contCohomologyClass_factorSet_eq`); and the
class vanishes exactly when the extension has a continuous homomorphic section
(`TauCeti.GroupExtension.exists_splitting_continuous_iff_contCohomologyClass_factorSet_eq_zero`).
For a **profinite** extension with compact kernel a continuous normalized section always exists, so
the class is an invariant of the extension itself, `GroupExtension.contCohomologyClass`, and the
two theorems take their final form
(`GroupExtension.exists_equiv_continuous_iff_contCohomologyClass_eq`,
`GroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero`). When `G` and `M`
are both profinite the twisted product of a continuous factor set is such an extension, the bundled
`TauCeti.ProfiniteGroupExtension.ofFactorSet` of
`TauCeti/Topology/Algebra/GroupExtension/Profinite.lean`, and its class, read through the canonical
section, is the class of the factor set
(`TauCeti.ProfiniteGroupExtension.contCohomologyClass_ofFactorSet`), so every class of `H²(G, M)`
is the class of a profinite extension. On the bundled profinite extensions
`TauCeti.ProfiniteGroupExtension` of `G` by `M` inducing the given action, the class therefore
descends to the bijection `TauCeti.ProfiniteGroupExtension.contCohomologyClassEquiv` from the
profinite extensions modulo continuous equivalence onto `H²(G, M)`. The trivial class is that of
the trivial factor set (`TauCeti.FactorSet.contCohomologyClass_trivial`), whose twisted product is
the semidirect product.

The classification is natural in the coefficient module. A continuous `G`-equivariant homomorphism
`f : M →*[G] N` of profinite modules pushes a factor set forward (`TauCeti.FactorSet.map`) and a
profinite extension forward (`TauCeti.ProfiniteGroupExtension.map`, the twisted product of the
pushforward of the factor set of a continuous section), and in both cases the class of the
pushforward is the image of the class under the coefficient map
`TauCeti.ContCohomology.explicitCoeff2` of `f`, read additively
(`TauCeti.FactorSet.contCohomologyClass_map`,
`TauCeti.ProfiniteGroupExtension.contCohomologyClass_map`). So the bijection commutes with
pushforward (`MulDistribMulActionHom.profiniteGroupExtensionContCohomologyClassEquiv_map`).

Naturality also compares extensions by *different* kernels (Neukirch–Schmidt–Wingberg, I §5
Exercise 4, at `ϕ = id`). The extension `X` maps to its pushforward `X.map f hf` by a canonical
continuous homomorphism over the identity of `G` restricting to `f` on the kernels
(`TauCeti.ProfiniteGroupExtension.mapHom`). Hence, if `f` carries the class of `X` to the class of
an extension `Y` by `N`, then `f` is the restriction to the kernels of a continuous homomorphism
`X.E → Y.E` over the identity of `G`
(`TauCeti.ProfiniteGroupExtension.exists_continuous_monoidHom_of_contCohomologyClass_map_eq`);
conversely such a homomorphism forces `f` to carry the class of `X` to the class of `Y`
(`TauCeti.ProfiniteGroupExtension.contCohomologyClass_map_eq_of_continuous_monoidHom`). When `f`
is surjective the lift is surjective too, by `GroupExtension.surjective_of_comp_inl_eq`.

The coboundaries here are those of the *continuous* complex, `B²` being the image of the
continuous `1`-cochains; this is what makes the classification a statement about topological
extensions. The abstract classification of `TauCeti/GroupTheory/GroupExtension/Cohomology.lean`
divides by all coboundaries and classifies abstract extensions. The continuous and the abstract
class of a factor set are different invariants, and it is the continuous one that the cohomology of
a profinite group computes with.

## Main definitions

* `TauCeti.FactorSet.contCohomologyClass`: the class of a continuous factor set in `H²(G, M)`.
* `TauCeti.FactorSet.IsContCohomologous`: two factor sets whose quotient is a continuous coboundary,
  with `TauCeti.FactorSet.isContCohomologousSetoid` the equivalence relation it cuts out on
  continuous factor sets.
* `TauCeti.FactorSet.contCohomologyClassEquiv`: **`H²(G, M)` classifies continuous factor sets up to
  continuous cohomology.**
* `GroupExtension.contCohomologyClass`: the class of a profinite extension with compact kernel,
  in the root namespace so that it is available as `S.contCohomologyClass`.
* `TauCeti.ProfiniteGroupExtension.continuousEquivSetoid`: continuous equivalence of bundled
  profinite extensions, the kernel of the class map.
* `TauCeti.ProfiniteGroupExtension.contCohomologyClassEquiv`: **`H²(G, M)` classifies profinite
  extensions of `G` by `M` inducing the given action up to continuous equivalence**, as a
  bijection of sets.
* `TauCeti.ProfiniteGroupExtension.continuousSection`: a continuous normalized section of a
  profinite extension with compact kernel, chosen once and for all.
* `TauCeti.ProfiniteGroupExtension.map`: the pushforward of a profinite extension along a
  continuous equivariant homomorphism of profinite coefficient modules, and
  `TauCeti.ProfiniteGroupExtension.mapHom`, the canonical continuous homomorphism from the
  extension to its pushforward.

## Main results

* `TauCeti.FactorSet.contCohomologyClass_eq_iff` and
  `TauCeti.FactorSet.exists_contCohomologyClass_eq`: the class is a complete invariant modulo
  continuous coboundaries, and it takes every value.
* `TauCeti.GroupExtension.contCohomologyClass_factorSet_eq`: the class of the factor set of a
  continuous normalized section does not depend on the section.
* `GroupExtension.exists_equiv_continuous_iff_contCohomologyClass_eq`: **`H²(G, M)` classifies
  profinite extensions of `G` by `M` inducing the given action, up to continuous equivalence.**
* `GroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero`: **a profinite
  extension has a continuous homomorphic section exactly when its class vanishes.**
* `TauCeti.ProfiniteGroupExtension.exists_contCohomologyClass_eq`: for profinite `G` and `M`,
  every class of `H²(G, M)` is the class of a profinite extension.
* `TauCeti.ProfiniteGroupExtension.subsingleton_H2_of_forall_exists_splitting`: for profinite `G`
  and `M`, if every profinite extension of `G` by `M` splits continuously then `H²(G, M) = 0`.
* `TauCeti.FactorSet.contCohomologyClass_map` and
  `MulDistribMulActionHom.profiniteGroupExtensionContCohomologyClassEquiv_map`:
  **the classification is natural in the coefficient module**: the class of a pushforward is the
  image of the class under the coefficient map.
* `TauCeti.ProfiniteGroupExtension.exists_continuous_monoidHom_of_contCohomologyClass_map_eq` and
  `TauCeti.ProfiniteGroupExtension.contCohomologyClass_map_eq_of_continuous_monoidHom`: **lifting
  a coefficient map along the class**: a continuous equivariant `f : M → N` is the restriction to
  the kernels of a continuous homomorphism of extensions over the identity of `G` exactly when it
  carries the class of the source to the class of the target.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §2, for the
  correspondence between extensions of profinite groups and continuous `2`-cocycles, and Ch. I §5
  Exercise 4 for lifting a coefficient map along the class.
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., Ch. 6 §8.
-/

public section

namespace TauCeti

universe u v w

open ContCohomology Topology

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [CommGroup M]
  [TopologicalSpace M] [MulDistribMulAction G M] [IsTopologicalGroup M]

namespace FactorSet

/-! ### Continuous factor sets as continuous cocycles -/

section Cocycle

variable (α β : FactorSet G M) (hα : Continuous ⇑α)

/-- A continuous factor set, read additively, as a continuous `2`-cocycle of the explicit complex
of continuous cochains. -/
def toZ2 : Z2 G (Additive M) :=
  ⟨fun p => Additive.ofMul (α p), (ofMul_mem_Z2_iff α).2 hα⟩

@[simp]
theorem coe_toZ2 : (α.toZ2 hα : G × G → Additive M) = fun p => Additive.ofMul (α p) :=
  (rfl)

/-- **Continuously cohomologous factor sets**: their pointwise quotient, read additively, is the
coboundary of a *continuous* `1`-cochain, that is, it lies in `B²` of the explicit complex of
continuous cochains. -/
def IsContCohomologous : Prop :=
  (fun p : G × G => Additive.ofMul (α p / β p)) ∈ B2 G (Additive M)

/-- Being continuously cohomologous, spelled multiplicatively: the quotient of the two factor sets
is the coboundary `(g, h) ↦ g • x h / x (g * h) * x g` of a continuous `x : G → M`. -/
theorem isContCohomologous_iff :
    IsContCohomologous α β ↔ ∃ x : G → M, Continuous x ∧
      ∀ g h : G, g • x h / x (g * h) * x g = α (g, h) / β (g, h) := by
  rw [IsContCohomologous, mem_B2_iff']
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun g => (c g).toMul, continuous_toMul.comp hc, fun g h' => ?_⟩
    simpa [toMul_add, toMul_sub] using congrArg Additive.toMul (h g h')
  · rintro ⟨x, hx, h⟩
    refine ⟨fun g => Additive.ofMul (x g), continuous_ofMul.comp hx, fun g h' => ?_⟩
    rw [← h g h']
    simp [ofMul_div, ofMul_mul]

end Cocycle

/-! ### The class of a continuous factor set -/

section Class

variable [ContinuousMul G] [ContinuousSMul G M] (α β : FactorSet G M) (hα : Continuous ⇑α)
  (hβ : Continuous ⇑β)

/-- **The class of a continuous factor set** in the explicit continuous cohomology group
`H²(G, M)`. Two continuous factor sets have the same class exactly when they are continuously
cohomologous (`TauCeti.FactorSet.contCohomologyClass_eq_iff`), and every class arises this way
(`TauCeti.FactorSet.exists_contCohomologyClass_eq`). -/
def contCohomologyClass : H2 G (Additive M) :=
  H2pi G (Additive M) (α.toZ2 hα)

theorem contCohomologyClass_def :
    α.contCohomologyClass hα = H2pi G (Additive M) (α.toZ2 hα) :=
  (rfl)

/-- The class does not depend on the proof of continuity, so a factor set can be replaced by an
equal one underneath it. -/
theorem contCohomologyClass_congr {α β : FactorSet G M} (h : α = β) (hα : Continuous ⇑α) :
    α.contCohomologyClass hα = β.contCohomologyClass (h ▸ hα) := by
  subst h
  rfl

/-- **Two continuous factor sets have the same class exactly when they are continuously
cohomologous.** -/
theorem contCohomologyClass_eq_iff :
    α.contCohomologyClass hα = β.contCohomologyClass hβ ↔ IsContCohomologous α β := by
  have hsub : ((α.toZ2 hα : G × G → Additive M) - β.toZ2 hβ) =
      fun p : G × G => Additive.ofMul (α p / β p) := by
    ext p
    simp [ofMul_div]
  rw [contCohomologyClass_def, contCohomologyClass_def, H2pi, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.mk'_apply, H2pi_eq_iff, IsContCohomologous, hsub]

@[simp]
theorem contCohomologyClass_trivial (h : Continuous ⇑(trivial G M)) :
    (trivial G M).contCohomologyClass h = 0 := by
  have hz : (trivial G M).toZ2 h = 0 := Subtype.ext (funext fun _ => by simp)
  rw [contCohomologyClass_def, hz, map_zero]

/-- **The class of a continuous factor set vanishes exactly when it is the coboundary of a
continuous function.** -/
theorem contCohomologyClass_eq_zero_iff :
    α.contCohomologyClass hα = 0 ↔
      ∃ x : G → M, Continuous x ∧ ∀ g h : G, g • x h / x (g * h) * x g = α (g, h) := by
  rw [← contCohomologyClass_trivial continuous_trivial, contCohomologyClass_eq_iff,
    isContCohomologous_iff]
  simp

/-- **Every class in `H²(G, M)` is the class of a continuous factor set.** A continuous `2`-cocycle
need not be normalized; subtracting the coboundary of the constant `1`-cochain at its value at
`(1, 1)` normalizes it without moving its class. -/
theorem exists_contCohomologyClass_eq (c : H2 G (Additive M)) :
    ∃ (α : FactorSet G M) (hα : Continuous ⇑α), α.contCohomologyClass hα = c := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  set b : G × G → Additive M := d1 G (Additive M) fun _ => (z : G × G → Additive M) (1, 1)
    with hb_def
  have hb : b ∈ B2 G (Additive M) := mem_B2_iff.2 ⟨_, continuous_const, rfl⟩
  have hz' : (z : G × G → Additive M) - b ∈ Z2 G (Additive M) :=
    (Z2 G (Additive M)).sub_mem z.2 (B2_le_Z2 G (Additive M) hb)
  have hz'₁ : ((z : G × G → Additive M) - b) (1, 1) = 0 := by
    simp [hb_def, d1_apply]
  refine ⟨ofMemZ2 hz' hz'₁, continuous_ofMemZ2 hz' hz'₁, ?_⟩
  have hsub : ((ofMemZ2 hz' hz'₁).toZ2 (continuous_ofMemZ2 hz' hz'₁) : G × G → Additive M) - z
      = -b := by
    ext p
    simp
  rw [contCohomologyClass_def, H2pi, QuotientAddGroup.mk'_apply, H2pi_eq_iff, hsub]
  exact (B2 G (Additive M)).neg_mem hb

variable (G M) in
/-- Being continuously cohomologous is an equivalence relation on continuous factor sets: by
`TauCeti.FactorSet.contCohomologyClass_eq_iff` it is the kernel of the class map. -/
def isContCohomologousSetoid : Setoid {α : FactorSet G M // Continuous ⇑α} :=
  Setoid.ker fun α : {α : FactorSet G M // Continuous ⇑α} => α.1.contCohomologyClass α.2

@[simp]
theorem isContCohomologousSetoid_apply {α β : {α : FactorSet G M // Continuous ⇑α}} :
    isContCohomologousSetoid G M α β ↔ IsContCohomologous α.1 β.1 :=
  Setoid.ker_def.trans (contCohomologyClass_eq_iff α.1 β.1 α.2 β.2)

variable (G M) in
/-- **`H²(G, M)` classifies continuous factor sets up to continuous cohomology.** The class descends
to a bijection from the continuous factor sets of `G` with values in `M`, taken modulo the
continuously cohomologous relation, onto the explicit continuous cohomology group. -/
noncomputable def contCohomologyClassEquiv :
    Quotient (isContCohomologousSetoid G M) ≃ H2 G (Additive M) :=
  Setoid.quotientKerEquivOfSurjective _ fun c => by
    obtain ⟨α, hα, h⟩ := exists_contCohomologyClass_eq c
    exact ⟨⟨α, hα⟩, h⟩

@[simp]
theorem contCohomologyClassEquiv_apply_mk (α : {α : FactorSet G M // Continuous ⇑α}) :
    contCohomologyClassEquiv G M (Quotient.mk _ α) = α.1.contCohomologyClass α.2 :=
  (rfl)

/-- The class of the twisted product of `α`, read through its canonical section, is the class of
`α`, because `TauCeti.GroupExtension.factorSet_canonicalSection` reads `α` back off that section. -/
theorem contCohomologyClass_factorSet_canonicalSection
    (h : Continuous ⇑(GroupExtension.factorSet α.canonicalSection α.canonicalSection_one
      (GroupExtension.inducesAction_groupExtension α))) :
    (GroupExtension.factorSet α.canonicalSection α.canonicalSection_one
      (GroupExtension.inducesAction_groupExtension α)).contCohomologyClass h =
        α.contCohomologyClass hα :=
  contCohomologyClass_congr (GroupExtension.factorSet_canonicalSection α) h

end Class

/-! ### Naturality in the coefficient module -/

section Map

variable [ContinuousMul G] [ContinuousSMul G M] {N : Type*} [CommGroup N] [TopologicalSpace N]
  [IsTopologicalGroup N] [MulDistribMulAction G N] [ContinuousSMul G N] (α : FactorSet G M)
  (f : M →*[G] N) (hf : Continuous f) (hα : Continuous ⇑α)

/-- **The class of a continuous factor set is natural in the coefficient module**: the class of the
pushforward `α.map f` along a continuous equivariant homomorphism `f` is the image of the class of
`α` under the coefficient map `TauCeti.ContCohomology.explicitCoeff2` of `f`, read additively. -/
@[simp]
theorem contCohomologyClass_map :
    (α.map f).contCohomologyClass (α.continuous_map f hf hα) =
      explicitCoeff2 G (Additive M) f.toAdditive (f.continuous_toAdditive hf)
        (α.contCohomologyClass hα) := by
  rw [contCohomologyClass_def, contCohomologyClass_def, H2pi, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.mk'_apply, explicitCoeff2_mk]
  congr 1
  refine Subtype.ext (funext fun ⟨g, h⟩ => ?_)
  -- `explicitCoeff2_mk` coerces `f.toAdditive` to an additive homomorphism, which blocks a
  -- rewrite with `cocyclesMap2_apply`; supplying the cocycle and the pair by hand unifies it.
  refine Eq.trans ?_ (cocyclesMap2_apply G (Additive M) G (Additive N) (ContinuousMonoidHom.id G)
    _ _ _ (α.toZ2 hα) g h).symm
  simp

end Map

end FactorSet

namespace GroupExtension

variable {E : Type w} [Group E] [TopologicalSpace E] [ContinuousMul G] [ContinuousSMul G M]
  {S : GroupExtension M E G}

/-! ### The class of an extension with a continuous normalized section -/

section Section

variable [ContinuousMul E] [ContinuousInv E] (hinl : IsEmbedding ⇑S.inl) {σ σ' : S.Section}
  (hσ : σ 1 = 1) (hσ' : σ' 1 = 1) (hact : InducesAction S)

include hinl

omit [ContinuousMul G] [ContinuousSMul G M] in
/-- **Two continuous normalized sections give continuously cohomologous factor sets**: their
quotient is the coboundary of the difference of the sections, which is continuous. -/
theorem isContCohomologous_factorSet (hσc : Continuous ⇑σ) (hσ'c : Continuous ⇑σ') :
    FactorSet.IsContCohomologous (factorSet σ hσ hact) (factorSet σ' hσ' hact) :=
  (FactorSet.isContCohomologous_iff _ _).2 ⟨sectionDiff σ σ', continuous_sectionDiff hinl hσc hσ'c,
    fun g h => (factorSet_div_factorSet σ σ' hσ hσ' hact g h).symm⟩

/-- **The class of the factor set of a continuous normalized section does not depend on the
section**, so it is an invariant of the extension. -/
theorem contCohomologyClass_factorSet_eq (hσc : Continuous ⇑σ) (hσ'c : Continuous ⇑σ') :
    (factorSet σ hσ hact).contCohomologyClass (continuous_factorSet hinl hσc hσ hact) =
      (factorSet σ' hσ' hact).contCohomologyClass (continuous_factorSet hinl hσ'c hσ' hact) :=
  (FactorSet.contCohomologyClass_eq_iff _ _ _ _).2
    (isContCohomologous_factorSet hinl hσ hσ' hact hσc hσ'c)

/-- **An extension has a continuous homomorphic section exactly when the class of the factor set
of a continuous normalized section vanishes.** A continuous homomorphic section is a continuous
normalized section with trivial factor set; conversely a continuous primitive `x` of the factor set
of `σ` corrects `σ` to the homomorphic section `g ↦ inl (x g)⁻¹ * σ g`. -/
theorem exists_splitting_continuous_iff_contCohomologyClass_factorSet_eq_zero
    (hσc : Continuous ⇑σ) :
    (∃ s : S.Splitting, Continuous ⇑s) ↔
      (factorSet σ hσ hact).contCohomologyClass (continuous_factorSet hinl hσc hσ hact) = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    have hs₁ : s.toSection 1 = 1 := map_one s
    have hsc : Continuous ⇑s.toSection := hs
    have htriv : factorSet s.toSection hs₁ hact = FactorSet.trivial G M :=
      FactorSet.ext fun ⟨g, h⟩ => S.inl_injective (by
        rw [inl_factorSet, FactorSet.trivial_apply, map_one]
        exact mul_inv_eq_one.2 (map_mul s g h).symm)
    rw [contCohomologyClass_factorSet_eq hinl hσ hs₁ hact hσc hsc,
      FactorSet.contCohomologyClass_congr htriv, FactorSet.contCohomologyClass_trivial]
  · intro h
    obtain ⟨x, hx, hxα⟩ := (FactorSet.contCohomologyClass_eq_zero_iff _ _).1 h
    have hx₁ : x 1 = 1 := by simpa using hxα 1 1
    -- the identity in `M` behind the corrected section being a homomorphism
    have hM : ∀ g h : G,
        (x (g * h))⁻¹ = (x g)⁻¹ * g • (x h)⁻¹ * factorSet σ hσ hact (g, h) := by
      intro g h
      rw [← hxα g h, smul_inv', div_eq_mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    refine ⟨GroupExtension.Splitting.mk
      { toFun g := S.inl (x g)⁻¹ * σ g
        map_one' := by simp [hx₁, hσ]
        map_mul' g h := by
          have h1 : σ g * S.inl (x h)⁻¹ = S.inl (g • (x h)⁻¹) * σ g := by
            rw [inl_smul σ hact, inv_mul_cancel_right]
          have h2 : (σ g : E) * σ h = S.inl (factorSet σ hσ hact (g, h)) * σ (g * h) := by
            rw [inl_factorSet, inv_mul_cancel_right]
          calc S.inl (x (g * h))⁻¹ * σ (g * h)
              = S.inl (x g)⁻¹ * S.inl (g • (x h)⁻¹) *
                  (S.inl (factorSet σ hσ hact (g, h)) * σ (g * h)) := by
                rw [hM, map_mul, map_mul]
                group
            _ = S.inl (x g)⁻¹ * (σ g * S.inl (x h)⁻¹) * σ h := by
                rw [← h2, h1]
                group
            _ = S.inl (x g)⁻¹ * σ g * (S.inl (x h)⁻¹ * σ h) := by group }
      fun g => by simp [GroupExtension.rightHom_inl], (hinl.continuous.comp hx.inv).mul hσc⟩

end Section

section Equiv

variable {E' : Type*} [Group E'] [TopologicalSpace E'] [ContinuousMul E] [ContinuousInv E]
  [ContinuousMul E'] [ContinuousInv E'] {S' : GroupExtension M E' G}
  (hinl : IsEmbedding ⇑S.inl) (hinl' : IsEmbedding ⇑S'.inl) (hrh : Continuous S.rightHom)
  (hrh' : Continuous S'.rightHom) {σ : S.Section} {σ' : S'.Section} (hσc : Continuous ⇑σ)
  (hσ'c : Continuous ⇑σ') (hσ : σ 1 = 1) (hσ' : σ' 1 = 1) (hact : InducesAction S)
  (hact' : InducesAction S')

include hrh hrh'

/-- **Equal classes give a homeomorphic equivalence.** Two extensions of `G` by `M`, both inducing
the ambient action and both with continuous projection, embedded kernel and a continuous
normalized section, whose factor sets have the same class are equivalent by an equivalence that is
a homeomorphism: a continuous primitive of the quotient of the two factor sets rescales one twisted
product onto the other by `TauCeti.FactorSet.rescaleEquiv`, continuously in both directions, and
the comparison maps `TauCeti.GroupExtension.factorSetToGroupExtensionEquiv` with the extensions are
homeomorphisms. -/
theorem exists_equiv_isHomeomorph_of_contCohomologyClass_factorSet_eq
    (h : (factorSet σ hσ hact).contCohomologyClass (continuous_factorSet hinl hσc hσ hact) =
      (factorSet σ' hσ' hact').contCohomologyClass (continuous_factorSet hinl' hσ'c hσ' hact')) :
    ∃ e : S.Equiv S', IsHomeomorph ⇑e := by
  obtain ⟨x, hx, hxe⟩ := (FactorSet.isContCohomologous_iff _ _).1
    ((FactorSet.contCohomologyClass_eq_iff _ _ _ _).1 h)
  have hx' : ∀ g h : G, factorSet σ hσ hact (g, h) * x (g * h) =
      factorSet σ' hσ' hact' (g, h) * (g • x h * x g) := by
    intro g h
    have key := hxe g h
    rw [div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul] at key
    rw [← key, mul_comm]
  refine ⟨((factorSetToGroupExtensionEquiv σ hσ hact).symm.trans
    (FactorSet.rescaleEquiv _ _ x hx')).trans (factorSetToGroupExtensionEquiv σ' hσ' hact'),
    isHomeomorph_iff_exists_inverse.2 ⟨?_, _, EquivLike.left_inv _, EquivLike.right_inv _, ?_⟩⟩
  · exact (continuous_factorSetToGroupExtensionEquiv hinl'.continuous hσ'c hσ' hact').comp
      ((FactorSet.continuous_rescaleEquiv hx' hx).comp
        (continuous_factorSetToGroupExtensionEquiv_symm hinl hrh hσc hσ hact))
  · exact (continuous_factorSetToGroupExtensionEquiv hinl.continuous hσc hσ hact).comp
      ((FactorSet.continuous_rescaleEquiv_symm hx' hx).comp
        (continuous_factorSetToGroupExtensionEquiv_symm hinl' hrh' hσ'c hσ' hact'))

/-- **Continuous `H²` classifies extensions with continuous normalized sections.** Two extensions of
`G` by `M`, both inducing the ambient action and both with continuous projection, embedded kernel
and a continuous normalized section, are equivalent by a continuous equivalence exactly when the
classes of the factor sets of those sections agree.

Forwards, the transported section `e ∘ σ` is a continuous normalized section of `S'` with literally
the same factor set as `σ`, and the class of `S'` does not depend on the section it is read from.
Backwards, `TauCeti.GroupExtension.exists_equiv_isHomeomorph_of_contCohomologyClass_factorSet_eq`
even produces a homeomorphic equivalence. -/
theorem exists_equiv_continuous_iff_contCohomologyClass_factorSet_eq :
    (∃ e : S.Equiv S', Continuous ⇑e) ↔
      (factorSet σ hσ hact).contCohomologyClass (continuous_factorSet hinl hσc hσ hact) =
        (factorSet σ' hσ' hact').contCohomologyClass
          (continuous_factorSet hinl' hσ'c hσ' hact') := by
  constructor
  · rintro ⟨e, hec⟩
    -- `e ∘ σ` is a continuous normalized section of `S'` with the same factor set as `σ`
    let τ : S'.Section :=
      ⟨fun g => e (σ g), fun g => (GroupExtension.Equiv.rightHom_map e (σ g)).trans (by simp)⟩
    have hτ₁ : τ 1 = 1 := by simp [τ, hσ]
    have hτc : Continuous ⇑τ := hec.comp hσc
    have hfac : factorSet τ hτ₁ hact' = factorSet σ hσ hact := by
      ext ⟨g, h⟩
      refine S'.inl_injective ?_
      rw [inl_factorSet, ← GroupExtension.Equiv.map_inl e, inl_factorSet]
      simp [τ]
    rw [← contCohomologyClass_factorSet_eq hinl' hτ₁ hσ' hact' hτc hσ'c]
    exact FactorSet.contCohomologyClass_congr hfac.symm _
  · intro h
    obtain ⟨e, he⟩ := exists_equiv_isHomeomorph_of_contCohomologyClass_factorSet_eq hinl hinl' hrh
      hrh' hσc hσ'c hσ hσ' hact hact' h
    exact ⟨e, he.continuous⟩

end Equiv

/-! ### Profinite extensions -/

section Profinite

variable [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E] [CompactSpace M]
  [T2Space G]

/-- **The class of a profinite extension with compact kernel** in the explicit continuous
cohomology group `H²(G, M)`: the class of the factor set of any continuous normalized section, of
which `TauCeti.GroupExtension.exists_continuous_section` provides one. By
`GroupExtension.contCohomologyClass_eq` the choice of section does not matter. -/
noncomputable def _root_.GroupExtension.contCohomologyClass (S : GroupExtension M E G)
    (hinl : Continuous S.inl) (hrh : Continuous S.rightHom) (hact : InducesAction S) :
    H2 G (Additive M) :=
  (factorSet (exists_continuous_section hinl hrh).choose
    (exists_continuous_section hinl hrh).choose_spec.2 hact).contCohomologyClass
    (continuous_factorSet (hinl.isClosedEmbedding S.inl_injective).isEmbedding
      (exists_continuous_section hinl hrh).choose_spec.1 _ hact)

variable (S : GroupExtension M E G) (hinl : Continuous S.inl) (hrh : Continuous S.rightHom)
  (hact : InducesAction S)

/-- The class of a profinite extension is the class of the factor set of any continuous normalized
section. -/
theorem _root_.GroupExtension.contCohomologyClass_eq {σ : S.Section} (hσc : Continuous ⇑σ)
    (hσ : σ 1 = 1) :
    S.contCohomologyClass hinl hrh hact = (factorSet σ hσ hact).contCohomologyClass
      (continuous_factorSet (hinl.isClosedEmbedding S.inl_injective).isEmbedding hσc hσ hact) :=
  contCohomologyClass_factorSet_eq (hinl.isClosedEmbedding S.inl_injective).isEmbedding
    (exists_continuous_section hinl hrh).choose_spec.2 hσ hact
    (exists_continuous_section hinl hrh).choose_spec.1 hσc

/-- **Continuous `H²` classifies profinite extensions.** Two profinite extensions of `G` by the
compact kernel `M`, both inducing the ambient action, are equivalent by a continuous equivalence
exactly when their classes agree. Such an equivalence is automatically a homeomorphism, the total
groups being compact and Hausdorff (`TauCeti.GroupExtension.continuousMulEquivOfEquiv`). -/
theorem _root_.GroupExtension.exists_equiv_continuous_iff_contCohomologyClass_eq {E' : Type*}
    [Group E']
    [TopologicalSpace E'] [IsTopologicalGroup E'] [CompactSpace E'] [TotallyDisconnectedSpace E']
    (S' : GroupExtension M E' G) (hinl' : Continuous S'.inl) (hrh' : Continuous S'.rightHom)
    (hact' : InducesAction S') :
    (∃ e : S.Equiv S', Continuous ⇑e) ↔
      S.contCohomologyClass hinl hrh hact = S'.contCohomologyClass hinl' hrh' hact' := by
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_section hinl hrh
  obtain ⟨σ', hσ'c, hσ'⟩ := exists_continuous_section hinl' hrh'
  rw [S.contCohomologyClass_eq hinl hrh hact hσc hσ,
    S'.contCohomologyClass_eq hinl' hrh' hact' hσ'c hσ',
    ← exists_equiv_continuous_iff_contCohomologyClass_factorSet_eq
      (hinl.isClosedEmbedding S.inl_injective).isEmbedding
      (hinl'.isClosedEmbedding S'.inl_injective).isEmbedding hrh hrh' hσc hσ'c hσ hσ' hact hact']

/-- **A profinite extension has a continuous homomorphic section exactly when its class
vanishes.** -/
theorem _root_.GroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero :
    (∃ s : S.Splitting, Continuous ⇑s) ↔ S.contCohomologyClass hinl hrh hact = 0 := by
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_section hinl hrh
  rw [S.contCohomologyClass_eq hinl hrh hact hσc hσ]
  exact exists_splitting_continuous_iff_contCohomologyClass_factorSet_eq_zero
    (hinl.isClosedEmbedding S.inl_injective).isEmbedding hσ hact hσc

end Profinite

end GroupExtension

/-! ### The bijection -/

namespace ProfiniteGroupExtension

section Class

variable [ContinuousMul G] [ContinuousSMul G M] [CompactSpace M] [T2Space G]
  (X Y : ProfiniteGroupExtension G M)

/-- The class of a profinite extension with compact kernel, `GroupExtension.contCohomologyClass`,
read on the bundled extension. -/
noncomputable def contCohomologyClass : H2 G (Additive M) :=
  X.toGroupExtension.contCohomologyClass X.continuous_inl X.continuous_rightHom X.inducesAction

theorem contCohomologyClass_def :
    X.contCohomologyClass = X.toGroupExtension.contCohomologyClass X.continuous_inl
      X.continuous_rightHom X.inducesAction :=
  (rfl)

/-- Two profinite extensions are continuously equivalent exactly when their classes agree:
`GroupExtension.exists_equiv_continuous_iff_contCohomologyClass_eq` for bundled extensions. -/
theorem exists_equiv_continuous_iff_contCohomologyClass_eq :
    (∃ e : X.toGroupExtension.Equiv Y.toGroupExtension, Continuous ⇑e) ↔
      X.contCohomologyClass = Y.contCohomologyClass :=
  X.toGroupExtension.exists_equiv_continuous_iff_contCohomologyClass_eq X.continuous_inl
    X.continuous_rightHom X.inducesAction Y.toGroupExtension Y.continuous_inl Y.continuous_rightHom
    Y.inducesAction

variable (G M) in
/-- **Continuous equivalence of profinite extensions** is an equivalence relation on the profinite
extensions of `G` by `M` inducing the given action: by
`TauCeti.ProfiniteGroupExtension.exists_equiv_continuous_iff_contCohomologyClass_eq` it is the
kernel of the class map, and `TauCeti.ProfiniteGroupExtension.continuousEquivSetoid_apply` reads
it back as the existence of a continuous equivalence. -/
noncomputable def continuousEquivSetoid : Setoid (ProfiniteGroupExtension G M) :=
  Setoid.ker contCohomologyClass

@[simp]
theorem continuousEquivSetoid_apply :
    continuousEquivSetoid G M X Y ↔
      ∃ e : X.toGroupExtension.Equiv Y.toGroupExtension, Continuous ⇑e :=
  Setoid.ker_def.trans (exists_equiv_continuous_iff_contCohomologyClass_eq X Y).symm

end Class

section Realization

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G M]
  [CompactSpace M] [TotallyDisconnectedSpace M] (α : FactorSet G M) (hα : Continuous ⇑α)

/-- The class of the twisted product of `α` is the class of `α`: read it through the canonical
section, whose factor set is `α`. -/
@[simp]
theorem contCohomologyClass_ofFactorSet :
    (ofFactorSet α hα).contCohomologyClass = α.contCohomologyClass hα := by
  have := FactorSet.Extension.isTopologicalGroup hα
  rw [contCohomologyClass_def]
  -- Rewriting the extension alone would ill-type its continuity and action witnesses.
  -- The abbreviation keeps the witnesses definitionally equal across the projection.
  exact (α.groupExtension.contCohomologyClass_eq _ _ _ (FactorSet.continuous_canonicalSection α)
    α.canonicalSection_one).trans (FactorSet.contCohomologyClass_factorSet_canonicalSection α hα _)

/-- **Every class of `H²(G, M)` is the class of a profinite extension**, namely of the twisted
product of a continuous factor set representing it. -/
theorem exists_contCohomologyClass_eq (c : H2 G (Additive M)) :
    ∃ X : ProfiniteGroupExtension G M, X.contCohomologyClass = c := by
  obtain ⟨α, hα, h⟩ := FactorSet.exists_contCohomologyClass_eq c
  exact ⟨ofFactorSet α hα, (contCohomologyClass_ofFactorSet α hα).trans h⟩

/-- **`H²(G, M)` vanishes when every profinite extension splits**: every class is the class of a
profinite extension, and the class of an extension with a continuous homomorphic section is zero. -/
theorem subsingleton_H2_of_forall_exists_splitting
    (h : ∀ X : ProfiniteGroupExtension G M, ∃ s : X.toGroupExtension.Splitting, Continuous ⇑s) :
    Subsingleton (H2 G (Additive M)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨X, rfl⟩ := exists_contCohomologyClass_eq c
  rw [contCohomologyClass_def,
    ← X.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]
  exact h X

variable (G M) in
/-- **Continuous `H²` classifies profinite extensions**: the class descends to a bijection from the
profinite extensions of `G` by `M` inducing the given action, taken modulo continuous
equivalence, onto `H²(G, M)`. -/
noncomputable def contCohomologyClassEquiv :
    Quotient (continuousEquivSetoid G M) ≃ H2 G (Additive M) :=
  Setoid.quotientKerEquivOfSurjective _ exists_contCohomologyClass_eq

@[simp]
theorem contCohomologyClassEquiv_apply_mk (X : ProfiniteGroupExtension G M) :
    contCohomologyClassEquiv G M (Quotient.mk _ X) = X.contCohomologyClass :=
  (rfl)

end Realization

/-! ### The chosen section -/

section Section

variable [CompactSpace M] [T2Space G] (X : ProfiniteGroupExtension G M)

/-- **A continuous normalized section of a profinite extension with compact kernel**, chosen once
and for all from `TauCeti.GroupExtension.exists_continuous_section`. The pushforwards
`TauCeti.ProfiniteGroupExtension.map` of `X` are the twisted products of the pushforwards of the
factor set of this section. -/
noncomputable def continuousSection : X.toGroupExtension.Section :=
  (GroupExtension.exists_continuous_section X.continuous_inl X.continuous_rightHom).choose

omit [IsTopologicalGroup M] in
theorem continuous_continuousSection : Continuous ⇑X.continuousSection :=
  (GroupExtension.exists_continuous_section X.continuous_inl X.continuous_rightHom).choose_spec.1

omit [IsTopologicalGroup M] in
theorem continuousSection_one : X.continuousSection 1 = 1 :=
  (GroupExtension.exists_continuous_section X.continuous_inl X.continuous_rightHom).choose_spec.2

end Section

/-! ### Naturality in the coefficient module -/

section Map

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G M]
  [CompactSpace M] {N : Type*} [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction G N] [ContinuousSMul G N] [CompactSpace N] [TotallyDisconnectedSpace N]
  (X : ProfiniteGroupExtension G M) (f : M →*[G] N) (hf : Continuous f)

/-- **Pushforward of a profinite extension along a continuous equivariant homomorphism `f` to a
profinite coefficient module**: the twisted product of the pushforward along `f` of the factor set
of the chosen continuous normalized section `TauCeti.ProfiniteGroupExtension.continuousSection` of
`X`. Its class is the image of the class of `X` under the coefficient map of `f`
(`TauCeti.ProfiniteGroupExtension.contCohomologyClass_map`), which determines it up to continuous
equivalence, and `X` maps to it by the continuous homomorphism
`TauCeti.ProfiniteGroupExtension.mapHom` over the identity of `G`. -/
noncomputable def map : ProfiniteGroupExtension G N :=
  ofFactorSet
    ((GroupExtension.factorSet X.continuousSection X.continuousSection_one X.inducesAction).map f)
    (FactorSet.continuous_map _ f hf (GroupExtension.continuous_factorSet
      (X.continuous_inl.isClosedEmbedding X.toGroupExtension.inl_injective).isEmbedding
      X.continuous_continuousSection X.continuousSection_one X.inducesAction))

/-- **The class of a profinite extension is natural in the coefficient module**: the class of the
pushforward `X.map f hf` is the image of the class of `X` under the coefficient map
`TauCeti.ContCohomology.explicitCoeff2` of `f`, read additively. -/
@[simp]
theorem contCohomologyClass_map :
    (X.map f hf).contCohomologyClass =
      explicitCoeff2 G (Additive M) f.toAdditive (f.continuous_toAdditive hf)
        X.contCohomologyClass := by
  rw [map, contCohomologyClass_ofFactorSet, FactorSet.contCohomologyClass_map _ f hf,
    contCohomologyClass_def, X.toGroupExtension.contCohomologyClass_eq X.continuous_inl
      X.continuous_rightHom X.inducesAction X.continuous_continuousSection X.continuousSection_one]

/-- Pushforward respects continuous equivalence, so it descends to the quotient by
`TauCeti.ProfiniteGroupExtension.continuousEquivSetoid`. -/
theorem continuousEquivSetoid_map (X Y : ProfiniteGroupExtension G M)
    (f : M →*[G] N) (hf : Continuous f) (h : continuousEquivSetoid G M X Y) :
    continuousEquivSetoid G N (X.map f hf) (Y.map f hf) :=
  Setoid.ker_def.2 (by rw [contCohomologyClass_map, contCohomologyClass_map, Setoid.ker_def.1 h])

/-- **The classification is natural in the coefficient module**: the bijection
`TauCeti.ProfiniteGroupExtension.contCohomologyClassEquiv` commutes with pushforward along `f` on
the extensions and with the coefficient map of `f` on `H²`. -/
theorem _root_.MulDistribMulActionHom.profiniteGroupExtensionContCohomologyClassEquiv_map
    [TotallyDisconnectedSpace M] (f : M →*[G] N) (hf : Continuous f)
    (q : Quotient (continuousEquivSetoid G M)) :
    contCohomologyClassEquiv G N
        (Quotient.map' (fun X => X.map f hf) (fun X Y => X.continuousEquivSetoid_map Y f hf) q) =
      explicitCoeff2 G (Additive M) f.toAdditive (f.continuous_toAdditive hf)
        (contCohomologyClassEquiv G M q) :=
  Quotient.inductionOn q fun X => X.contCohomologyClass_map f hf

end Map

/-! ### Lifting a coefficient map along the class -/

section Lift

omit [IsTopologicalGroup M]

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [CompactSpace M]
  {N : Type*} [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N] [MulDistribMulAction G N]
  [ContinuousSMul G N] [CompactSpace N] [TotallyDisconnectedSpace N]
  (X : ProfiniteGroupExtension G M) (f : M →*[G] N) (hf : Continuous f)

/-- **The canonical homomorphism from a profinite extension to its pushforward**,
`X.E → (X.map f hf).E`: identify `X.E` with the twisted product of the factor set of its chosen
section, by the inverse of `TauCeti.GroupExtension.factorSetToGroupExtensionEquiv`, and apply `f`
to the `M`-coordinate (`TauCeti.FactorSet.mapExtension`). It is continuous
(`TauCeti.ProfiniteGroupExtension.continuous_mapHom`), covers the identity of `G`
(`TauCeti.ProfiniteGroupExtension.rightHom_mapHom`) and restricts to `f` on the kernels
(`TauCeti.ProfiniteGroupExtension.mapHom_inl`). -/
noncomputable def mapHom : X.E →* (X.map f hf).E :=
  ((GroupExtension.factorSet X.continuousSection X.continuousSection_one
      X.inducesAction).mapExtension f).comp
    (GroupExtension.factorSetToGroupExtensionEquiv X.continuousSection X.continuousSection_one
      X.inducesAction).symm.toMulEquiv.toMonoidHom

-- The bodies of `map` and `mapHom` are visible only inside this module, so the two unfolding
-- lemmas that the properties of `mapHom` rewrite with are private to it.

private theorem map_toGroupExtension :
    (X.map f hf).toGroupExtension =
      ((GroupExtension.factorSet X.continuousSection X.continuousSection_one
        X.inducesAction).map f).groupExtension :=
  (rfl)

private theorem mapHom_apply (x : X.E) :
    X.mapHom f hf x = (GroupExtension.factorSet X.continuousSection X.continuousSection_one
      X.inducesAction).mapExtension f
        ((GroupExtension.factorSetToGroupExtensionEquiv X.continuousSection
          X.continuousSection_one X.inducesAction).symm x) :=
  (rfl)

theorem continuous_mapHom : Continuous (X.mapHom f hf) :=
  (FactorSet.continuous_mapExtension _ f hf).comp
    (GroupExtension.continuous_factorSetToGroupExtensionEquiv_symm
      (X.continuous_inl.isClosedEmbedding X.toGroupExtension.inl_injective).isEmbedding
      X.continuous_rightHom X.continuous_continuousSection X.continuousSection_one
      X.inducesAction)

/-- The canonical homomorphism to the pushforward restricts to `f` on the kernels. -/
@[simp]
theorem mapHom_inl (m : M) :
    X.mapHom f hf (X.toGroupExtension.inl m) = (X.map f hf).toGroupExtension.inl (f m) := by
  rw [mapHom_apply, GroupExtension.Equiv.map_inl, map_toGroupExtension,
    FactorSet.groupExtension_inl, FactorSet.groupExtension_inl]
  exact DFunLike.congr_fun (FactorSet.mapExtension_comp_inl _ f) m

/-- The canonical homomorphism to the pushforward covers the identity of `G`. -/
@[simp]
theorem rightHom_mapHom (x : X.E) :
    (X.map f hf).toGroupExtension.rightHom (X.mapHom f hf x) = X.toGroupExtension.rightHom x := by
  rw [mapHom_apply, map_toGroupExtension, ← GroupExtension.Equiv.rightHom_map
    (GroupExtension.factorSetToGroupExtensionEquiv X.continuousSection X.continuousSection_one
      X.inducesAction).symm x, FactorSet.groupExtension_rightHom, FactorSet.groupExtension_rightHom]
  exact DFunLike.congr_fun (FactorSet.rightHom_comp_mapExtension _ f) _

theorem mapHom_comp_inl :
    (X.mapHom f hf).comp X.toGroupExtension.inl =
      (X.map f hf).toGroupExtension.inl.comp f.toMonoidHom :=
  MonoidHom.ext fun m => X.mapHom_inl f hf m

theorem rightHom_comp_mapHom :
    (X.map f hf).toGroupExtension.rightHom.comp (X.mapHom f hf) = X.toGroupExtension.rightHom :=
  MonoidHom.ext fun x => X.rightHom_mapHom f hf x

variable (Y : ProfiniteGroupExtension G N)

/-- **Lifting a coefficient map along the class** (Neukirch–Schmidt–Wingberg, I §5 Exercise 4,
at `ϕ = id`). Let `X` be a profinite extension of `G` by `M` and `Y` one by `N`. If the
continuous equivariant `f : M → N` carries the class of `X` to the class of `Y`, then `f` is the
restriction to the kernels of a continuous homomorphism `X.E → Y.E` over the identity of `G`.
The converse is
`TauCeti.ProfiniteGroupExtension.contCohomologyClass_map_eq_of_continuous_monoidHom`, and the
lift is surjective when `f` is, by `GroupExtension.surjective_of_comp_inl_eq`. -/
theorem exists_continuous_monoidHom_of_contCohomologyClass_map_eq
    (h : (X.map f hf).contCohomologyClass = Y.contCohomologyClass) :
    ∃ φ : X.E →* Y.E, Continuous φ ∧
      φ.comp X.toGroupExtension.inl = Y.toGroupExtension.inl.comp f.toMonoidHom ∧
      Y.toGroupExtension.rightHom.comp φ = X.toGroupExtension.rightHom := by
  -- The pushforward `X.map f hf` has the class of `Y`, so the classification gives a continuous
  -- equivalence `e` of it with `Y`; the lift is `e` composed with the canonical `X.mapHom f hf`.
  obtain ⟨e, he⟩ := (exists_equiv_continuous_iff_contCohomologyClass_eq (X.map f hf) Y).2 h
  refine ⟨e.toMulEquiv.toMonoidHom.comp (X.mapHom f hf), he.comp (X.continuous_mapHom f hf),
    ?_, ?_⟩
  · ext m
    simp
  · ext x
    simp

/-- **The converse of the lifting lemma.** A continuous homomorphism `φ : X.E → Y.E` over the
identity of `G` that restricts to the continuous equivariant `f` on the kernels carries the class
of `X` to the class of `Y`. The forward direction is
`TauCeti.ProfiniteGroupExtension.exists_continuous_monoidHom_of_contCohomologyClass_map_eq`. -/
theorem contCohomologyClass_map_eq_of_continuous_monoidHom (φ : X.E →* Y.E) (hφ : Continuous φ)
    (hinl : φ.comp X.toGroupExtension.inl = Y.toGroupExtension.inl.comp f.toMonoidHom)
    (hright : Y.toGroupExtension.rightHom.comp φ = X.toGroupExtension.rightHom) :
    (X.map f hf).contCohomologyClass = Y.contCohomologyClass := by
  -- `φ` transports the chosen continuous normalized section of `X` to a continuous normalized
  -- section of `Y` whose factor set is the pushforward along `f` of the factor set of `X`
  -- (`GroupExtension.factorSet_monoidHomComp`); both classes are then read off that factor set.
  have hσ' : X.continuousSection.monoidHomComp φ hright 1 = 1 := by
    simp [X.continuousSection_one]
  have hσ'c : Continuous ⇑(X.continuousSection.monoidHomComp φ hright) :=
    (hφ.comp X.continuous_continuousSection).congr fun g =>
      (GroupExtension.Section.monoidHomComp_apply X.continuousSection φ hright g).symm
  rw [map, contCohomologyClass_ofFactorSet, contCohomologyClass_def,
    Y.toGroupExtension.contCohomologyClass_eq Y.continuous_inl Y.continuous_rightHom
      Y.inducesAction hσ'c hσ']
  exact (FactorSet.contCohomologyClass_congr (GroupExtension.factorSet_monoidHomComp
    X.continuousSection X.continuousSection_one X.inducesAction Y.inducesAction f φ hinl hright)
    _).symm

end Lift

end ProfiniteGroupExtension

end TauCeti
