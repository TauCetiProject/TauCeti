/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Topology.Homeomorph.Congr
public import TauCeti.Topology.Homotopy.Isotopy.Comp

/-!
# The topological mapping class group

For a topological space `M`, the self-homeomorphisms of `M` isotopic to the identity, in the sense
of `TauCeti.Isotopic` (homotopies through topological embeddings), form a normal subgroup
`TauCeti.isotopicToIdSubgroup M` of the homeomorphism group `M ≃ₜ M`. The **topological mapping
class group** `TauCeti.MappingClassGroupFull M` is the quotient: the group of isotopy classes of
self-homeomorphisms of `M`, no condition being imposed on the boundary or on orientations.

The subgroup laws are the closure of isotopy under composition with homeomorphisms
(`TauCeti.Isotopic.precomp_homeomorph`, `TauCeti.Isotopic.postcomp_homeomorph`). If `F` joins `f`
to the identity and `G` joins `g` to the identity, then `F ∘ g` followed by `G` joins `f ∘ g` to
the identity; `f⁻¹ ∘ F` joins the identity to `f⁻¹`; and `h ∘ F ∘ h⁻¹` joins `h ∘ f ∘ h⁻¹` to the
identity. Every slice stays an embedding, and no continuity of `(t, x) ↦ F_t⁻¹ x` is needed, which
can fail off compact spaces.

The boundary of a manifold is allowed to move, unlike in the smooth mapping class group
`TauCeti.MappingClassGroup`, whose diffeomorphisms and isotopies fix it pointwise. The forgetful
homomorphism from the smooth group is `TauCeti.MappingClassGroup.toMappingClassGroupFull`.

## Main definitions

* `TauCeti.isotopicToIdSubgroup M`: the normal subgroup of homeomorphisms isotopic to the
  identity.
* `TauCeti.MappingClassGroupFull M`: the topological mapping class group, the quotient of
  `M ≃ₜ M` by `isotopicToIdSubgroup M`.
* `TauCeti.MappingClassGroupFull.mk M`: the quotient homomorphism
  `(M ≃ₜ M) →* MappingClassGroupFull M`.
* `TauCeti.MappingClassGroupFull.lift`: a homomorphism out of `M ≃ₜ M` trivial on every
  homeomorphism isotopic to the identity descends to `MappingClassGroupFull M`.
* `TauCeti.MappingClassGroupFull.congr e`: the isomorphism of mapping class groups induced by a
  homeomorphism `e : M ≃ₜ N`, conjugating representatives by `e`.

## Main results

* `TauCeti.mem_isotopicToIdSubgroup`: membership is isotopy to the identity.
* `TauCeti.homeoCongr_mem_isotopicToIdSubgroup_iff`: conjugation by a homeomorphism preserves
  isotopy to the identity.
* `TauCeti.MappingClassGroupFull.mk_eq_mk_iff`: two homeomorphisms have the same class exactly
  when they are isotopic.
* `TauCeti.MappingClassGroupFull.mk_finalHomeomorph_eq_one`: the final homeomorphism of an
  ambient isotopy represents the trivial class.
* `TauCeti.MappingClassGroupFull.lift_mk`, `TauCeti.MappingClassGroupFull.hom_ext`: the universal
  property of `mk`.

## References

* B. Farb and D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.1.
-/

public section

open Topology

namespace TauCeti

variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

variable (M) in
/-- The homeomorphisms of `M` isotopic to the identity, in the sense of `TauCeti.Isotopic`, form a
subgroup of `M ≃ₜ M`. It is normal (`TauCeti.isotopicToIdSubgroup.normal`). -/
def isotopicToIdSubgroup : Subgroup (M ≃ₜ M) where
  carrier := {f | Isotopic (f : C(M, M)) (ContinuousMap.id M)}
  one_mem' := Isotopic.refl _ IsEmbedding.id
  mul_mem' {f g} hf hg := by
    -- `F_t ∘ g` joins `f ∘ g` to `g`, and `G_t` joins `g` to the identity.
    simpa using ((hf : Isotopic (f : C(M, M)) _).precomp_homeomorph g).trans hg
  inv_mem' {f} hf := by
    -- `f⁻¹ ∘ F_t` joins the identity to `f⁻¹`.
    simpa using ((hf : Isotopic (f : C(M, M)) _).postcomp_homeomorph f.symm).symm

/-- A homeomorphism lies in `isotopicToIdSubgroup M` exactly when it is isotopic to the
identity. -/
@[simp]
theorem mem_isotopicToIdSubgroup {f : M ≃ₜ M} :
    f ∈ isotopicToIdSubgroup M ↔ Isotopic (f : C(M, M)) (ContinuousMap.id M) :=
  Iff.rfl

/-- Conjugating a homeomorphism isotopic to the identity by a homeomorphism `e : M ≃ₜ N` gives a
homeomorphism isotopic to the identity: `e ∘ F_t ∘ e⁻¹` joins `e ∘ f ∘ e⁻¹` to the identity. -/
theorem homeoCongr_mem_isotopicToIdSubgroup (e : M ≃ₜ N) {f : M ≃ₜ M}
    (hf : f ∈ isotopicToIdSubgroup M) : Homeomorph.homeoCongr e f ∈ isotopicToIdSubgroup N := by
  rw [mem_isotopicToIdSubgroup] at hf ⊢
  simpa using (hf.precomp_homeomorph e.symm).postcomp_homeomorph e

/-- Conjugation by a homeomorphism `e : M ≃ₜ N` preserves isotopy to the identity. -/
theorem homeoCongr_mem_isotopicToIdSubgroup_iff (e : M ≃ₜ N) {f : M ≃ₜ M} :
    Homeomorph.homeoCongr e f ∈ isotopicToIdSubgroup N ↔ f ∈ isotopicToIdSubgroup M := by
  refine ⟨fun h => ?_, homeoCongr_mem_isotopicToIdSubgroup e⟩
  simpa [← Homeomorph.homeoCongr_symm] using homeoCongr_mem_isotopicToIdSubgroup e.symm h

/-- Conjugation by a homeomorphism `e : M ≃ₜ N` carries the homeomorphisms of `M` isotopic to the
identity onto those of `N`. -/
theorem map_homeoCongr_isotopicToIdSubgroup (e : M ≃ₜ N) :
    (isotopicToIdSubgroup M).map (Homeomorph.homeoCongr e : (M ≃ₜ M) →* (N ≃ₜ N)) =
      isotopicToIdSubgroup N := by
  ext f
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, Homeomorph.homeoCongr_symm]
  exact homeoCongr_mem_isotopicToIdSubgroup_iff e.symm

/-- The homeomorphisms isotopic to the identity form a normal subgroup: `h ∘ F_t ∘ h⁻¹` joins
`h ∘ f ∘ h⁻¹` to the identity. -/
instance isotopicToIdSubgroup.normal : (isotopicToIdSubgroup M).Normal where
  conj_mem f hf h := by
    have hconj : h * f * h⁻¹ = Homeomorph.homeoCongr h f := by ext; simp
    rw [hconj]
    exact homeoCongr_mem_isotopicToIdSubgroup h hf

/-- The final homeomorphism of an ambient isotopy is isotopic to the identity. -/
theorem finalHomeomorph_mem_isotopicToIdSubgroup (Φ : AmbientIsotopy M) :
    Φ.finalHomeomorph ∈ isotopicToIdSubgroup M := by
  simpa using (Φ.isotopic (f := ContinuousMap.id M) IsEmbedding.id).symm

variable (M) in
/-- The **topological mapping class group** of `M`: the group of isotopy classes of
self-homeomorphisms of `M`, the quotient of `M ≃ₜ M` by the normal subgroup of homeomorphisms
isotopic to the identity. Neither the boundary nor an orientation is fixed. -/
def MappingClassGroupFull : Type _ :=
  (M ≃ₜ M) ⧸ isotopicToIdSubgroup M

namespace MappingClassGroupFull

instance : Group (MappingClassGroupFull M) :=
  inferInstanceAs (Group ((M ≃ₜ M) ⧸ isotopicToIdSubgroup M))

instance : Inhabited (MappingClassGroupFull M) := ⟨1⟩

variable (M) in
/-- The quotient homomorphism sending a homeomorphism to its mapping class. -/
def mk : (M ≃ₜ M) →* MappingClassGroupFull M :=
  QuotientGroup.mk' _

/-- Every mapping class is the class of a homeomorphism. -/
theorem mk_surjective : Function.Surjective (mk M) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the quotient map is the subgroup of homeomorphisms isotopic to the identity. -/
@[simp]
theorem ker_mk : (mk M).ker = isotopicToIdSubgroup M :=
  QuotientGroup.ker_mk' _

/-- A homeomorphism represents the trivial mapping class exactly when it is isotopic to the
identity. -/
theorem mk_eq_one_iff {f : M ≃ₜ M} :
    mk M f = 1 ↔ Isotopic (f : C(M, M)) (ContinuousMap.id M) := by
  rw [← MonoidHom.mem_ker, ker_mk, mem_isotopicToIdSubgroup]

/-- Two homeomorphisms have the same mapping class exactly when they are isotopic. -/
theorem mk_eq_mk_iff {f g : M ≃ₜ M} : mk M f = mk M g ↔ Isotopic (f : C(M, M)) g := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff, div_eq_mul_inv]
  -- Composing on the right with `g` or with `g⁻¹` moves between `f ∘ g⁻¹ ≃ id` and `f ≃ g`.
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [ContinuousMap.comp_assoc] using h.precomp_homeomorph g
  · simpa [ContinuousMap.comp_assoc] using h.precomp_homeomorph g.symm

/-- The final homeomorphism of an ambient isotopy represents the trivial mapping class. -/
@[simp]
theorem mk_finalHomeomorph_eq_one (Φ : AmbientIsotopy M) : mk M Φ.finalHomeomorph = 1 :=
  (QuotientGroup.eq_one_iff _).2 (finalHomeomorph_mem_isotopicToIdSubgroup Φ)

section Lift

variable {G : Type*} [Group G]

/-- A homomorphism out of `M ≃ₜ M` that is trivial on every homeomorphism isotopic to the
identity descends to the mapping class group. -/
def lift (φ : (M ≃ₜ M) →* G)
    (hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1) :
    MappingClassGroupFull M →* G :=
  QuotientGroup.lift _ φ hφ

/-- The descended homomorphism sends the class of `f` to `φ f`. -/
@[simp]
theorem lift_mk (φ : (M ≃ₜ M) →* G)
    (hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1) (f : M ≃ₜ M) :
    lift φ hφ (mk M f) = φ f :=
  QuotientGroup.lift_mk' _ _ f

/-- The descended homomorphism composed with `mk` is `φ`. -/
@[simp]
theorem lift_comp_mk (φ : (M ≃ₜ M) →* G)
    (hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1) :
    (lift φ hφ).comp (mk M) = φ :=
  MonoidHom.ext (lift_mk φ hφ)

/-- Two homomorphisms out of the mapping class group agreeing on every class `mk M f` are
equal. -/
@[ext]
theorem hom_ext {ψ ψ' : MappingClassGroupFull M →* G} (h : ψ.comp (mk M) = ψ'.comp (mk M)) :
    ψ = ψ' :=
  QuotientGroup.monoidHom_ext _ h

/-- The descended homomorphism is the only one whose composite with `mk` is `φ`. -/
theorem eq_lift_iff {φ : (M ≃ₜ M) →* G}
    {hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1}
    {ψ : MappingClassGroupFull M →* G} : ψ = lift φ hφ ↔ ψ.comp (mk M) = φ :=
  ⟨fun h => h ▸ lift_comp_mk φ hφ, fun h => hom_ext (h.trans (lift_comp_mk φ hφ).symm)⟩

end Lift

section Congr

/-- A homeomorphism `e : M ≃ₜ N` induces an isomorphism of mapping class groups, sending the class
of `f` to the class of `e ∘ f ∘ e⁻¹`. -/
def congr (e : M ≃ₜ N) : MappingClassGroupFull M ≃* MappingClassGroupFull N :=
  QuotientGroup.congr _ _ (Homeomorph.homeoCongr e) (map_homeoCongr_isotopicToIdSubgroup e)

/-- The induced isomorphism sends the class of `f` to the class of `e ∘ f ∘ e⁻¹`. -/
@[simp]
theorem congr_mk (e : M ≃ₜ N) (f : M ≃ₜ M) :
    congr e (mk M f) = mk N (Homeomorph.homeoCongr e f) :=
  QuotientGroup.congr_mk' _ _ _ _ _

/-- The isomorphism induced by the identity homeomorphism is the identity. -/
@[simp]
theorem congr_refl : congr (Homeomorph.refl M) = MulEquiv.refl (MappingClassGroupFull M) := by
  ext φ
  obtain ⟨f, rfl⟩ := mk_surjective φ
  simp

/-- The isomorphism induced by a composite homeomorphism is the composite of the induced
isomorphisms. -/
@[simp]
theorem congr_trans (e : M ≃ₜ N) (e' : N ≃ₜ P) :
    congr (e.trans e') = (congr e).trans (congr e') := by
  ext φ
  obtain ⟨f, rfl⟩ := mk_surjective φ
  simp

/-- The isomorphism induced by `e.symm` is the inverse of the one induced by `e`. -/
@[simp]
theorem congr_symm (e : M ≃ₜ N) : (congr e).symm = congr e.symm := by
  ext φ
  obtain ⟨f, rfl⟩ := mk_surjective φ
  simp [MulEquiv.symm_apply_eq, ← Homeomorph.homeoCongr_symm]

end Congr

end MappingClassGroupFull

end TauCeti
