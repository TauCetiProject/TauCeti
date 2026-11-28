/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.Smooth.Category
public import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# Compact induction of smooth representations

`Representation.compactInduction` is the subrepresentation of Mathlib's `Representation.coind`
consisting of smooth vectors with compact support modulo the inducing subgroup. We use the
coset space `G ⧸ H` via `g ↦ g⁻¹H`. Functions satisfy left covariance and `G` acts by translation.
`Representation.compactInduction_eq_smoothVectors` gives equality with smooth coinduction when
the coset space is compact. `TauCeti.SmoothRep.cIndFunctor` acts by postcomposition on morphisms
and is linear over commutative coefficient rings.

## References

* W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, §2.4.
* C. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, §2.5.
-/

public section

open Set Function

namespace Representation

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {H : Subgroup G} {σ : Representation A H V} {τ : Representation A H W}

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Inverting the argument of a smooth coinduced function gives a locally constant function.
The open stabilizer provides neighbourhoods even when inversion is not assumed continuous. -/
theorem isLocallyConstant_coindV_inv_of_mem_smoothVectors {f : σ.coindV H.subtype}
    (hf : f ∈ (σ.coind H.subtype).smoothVectors) : IsLocallyConstant fun x : G ↦ f.val x⁻¹ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(· * x⁻¹) ⁻¹' ((σ.coind H.subtype).stabilizer f : Set G),
    (mem_smoothVectors_iff.1 hf).preimage (continuous_mul_const _), by simp, ?_⟩
  intro y hy
  have hm : y * x⁻¹ ∈ (σ.coind H.subtype).stabilizer f := hy
  have hi : x * y⁻¹ ∈ (σ.coind H.subtype).stabilizer f := by
    simpa only [mul_inv_rev, inv_inv] using Subgroup.inv_mem _ hm
  have h := congrArg (fun v : σ.coindV H.subtype ↦ v.val x⁻¹) (mem_stabilizer.1 hi)
  simpa only [coind_apply_coe_apply, inv_mul_cancel_left] using h

/-- The support modulo `H` of a smooth vector of coinduction is closed. -/
theorem isClosed_coindSupport_of_mem_smoothVectors {f : σ.coindV H.subtype}
    (hf : f ∈ (σ.coind H.subtype).smoothVectors) : IsClosed (coindSupport f) := by
  apply (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage.1
  have hs : (QuotientGroup.mk : G → G ⧸ H) ⁻¹' coindSupport f =
      support (fun x : G ↦ f.val x⁻¹) := by
    ext g
    have h := coindSupport_mk_inv_mem_iff (f := f) (g := g⁻¹)
    simpa only [Set.mem_preimage, mem_support, inv_inv] using h
  rw [hs]
  exact (LocallyConstant.isClopen_support
    ⟨_, isLocallyConstant_coindV_inv_of_mem_smoothVectors hf⟩).isClosed

variable (σ) in
/-- Compact induction from `H` consists of the smooth vectors in coinduction whose support
modulo `H` is compact. -/
def compactInduction : Subrepresentation (σ.coind H.subtype) where
  toSubmodule := let S := (σ.coind H.subtype).smoothVectors
    { carrier := {f | f ∈ S ∧ IsCompact (coindSupport f)}
      add_mem' := fun {f k} hf hk ↦ by
        have hs := S.toSubmodule.add_mem hf.1 hk.1
        refine ⟨hs, (hf.2.union hk.2).of_isClosed_subset
          (isClosed_coindSupport_of_mem_smoothVectors hs) ?_⟩
        simp only [coindSupport_def, ← Set.image_union]
        exact Set.image_mono (support_add f.val k.val)
      zero_mem' := ⟨S.toSubmodule.zero_mem,
        (coindSupport_zero (σ := σ)).symm ▸ isCompact_empty⟩
      smul_mem' := fun c f hf ↦ by
        have hs := S.toSubmodule.smul_mem c hf.1
        refine ⟨hs, hf.2.of_isClosed_subset (isClosed_coindSupport_of_mem_smoothVectors hs) ?_⟩
        simpa only [coindSupport_def, Submodule.coe_smul] using
          Set.image_mono (support_const_smul_subset c f.val) }
  apply_mem_toSubmodule g f hf :=
    ⟨apply_mem_smoothVectors hf.1 g, coindSupport_coind_apply f g ▸
      hf.2.image (continuous_const_smul g)⟩

/-- Membership in compact induction is smoothness and compactness of support modulo `H`. -/
@[simp] theorem mem_compactInduction_iff {f : σ.coindV H.subtype} :
    f ∈ σ.compactInduction ↔
      f ∈ (σ.coind H.subtype).smoothVectors ∧ IsCompact (coindSupport f) :=
  (Iff.rfl)

-- The existing simplifier lemmas expand the coinduced action before this rule can fire.
/-- The action of `g` in compact induction is right translation by `g`. -/
theorem compactInduction_apply_apply (f : σ.compactInduction.toSubmodule) (g x : G) :
    (σ.compactInduction.toRepresentation g f).val.val x = f.val.val (x * g) := by
  rw [Subrepresentation.coe_toRepresentation_apply, coind_apply_coe_apply]

/-- Compact induction is a smooth representation. -/
instance : σ.compactInduction.toRepresentation.IsSmooth where
  isOpen_stabilizer f := σ.compactInduction.stabilizer_toRepresentation f ▸
    mem_smoothVectors_iff.1 (mem_compactInduction_iff.1 f.property).1

/-- If the coset space is compact, compact induction equals smooth coinduction. -/
theorem compactInduction_eq_smoothVectors (σ : Representation A H V) [CompactSpace (G ⧸ H)] :
    σ.compactInduction = (σ.coind H.subtype).smoothVectors := by
  ext f
  exact mem_compactInduction_iff.trans
    ⟨And.left, fun hf ↦ ⟨hf, (isClosed_coindSupport_of_mem_smoothVectors hf).isCompact⟩⟩

/-- Postcomposition by an intertwining map of coefficients restricts to compact induction. -/
def compactInductionMap (φ : σ.IntertwiningMap τ) :
    σ.compactInduction.toRepresentation.IntertwiningMap τ.compactInduction.toRepresentation :=
  ((coindMap H.subtype φ).comp σ.compactInduction.subtype).codRestrict _ fun f ↦ by
    simp only [IntertwiningMap.comp_apply, Subrepresentation.coe_subtype]
    have hf := mem_compactInduction_iff.1 f.property
    have hs := (coindMap H.subtype φ).apply_mem_smoothVectors hf.1
    refine mem_compactInduction_iff.2
      ⟨hs, hf.2.of_isClosed_subset (isClosed_coindSupport_of_mem_smoothVectors hs) ?_⟩
    simp only [coindSupport_def]
    exact Set.image_mono (support_comp_subset (map_zero φ) f.val.val)

/-- On left-covariant functions the induced map acts by postcomposition. -/
@[simp]
theorem compactInductionMap_apply_apply (φ : σ.IntertwiningMap τ)
    (f : σ.compactInduction.toSubmodule) (g : G) :
    (compactInductionMap φ f).val.val g = φ (f.val.val g) := by
  rw [compactInductionMap, IntertwiningMap.codRestrict_apply_coe, IntertwiningMap.comp_apply,
    Subrepresentation.coe_subtype, coindMap_coe_apply_apply]
end Representation

namespace TauCeti.SmoothRep

open CategoryTheory
universe u v w
variable {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Compact induction on smooth representations, with postcomposition on morphisms. -/
-- As for `smoothPart`, the object carrier must reduce to the subrepresentation for evaluation.
abbrev cIndFunctor (A : Type u) [Ring A] (H : Subgroup G) :
    SmoothRep.{max v w} A H ⥤ SmoothRep.{max v w} A G where
  obj X := SmoothRep.of (V := X.obj.ρ.compactInduction.toSubmodule)
    X.obj.ρ.compactInduction.toRepresentation
  map f := ObjectProperty.homMk (Rep.ofHom (Representation.compactInductionMap f.hom.hom))
  map_id X := ObjectProperty.hom_ext _ (Rep.hom_ext (by
    ext x g
    simp))
  map_comp f g := ObjectProperty.hom_ext _ (Rep.hom_ext (by
    ext x h
    simp))

/-- The object of the compact induction functor carries the compactly supported coinduced action. -/
@[simp] theorem cIndFunctor_obj (A : Type u) [Ring A] (H : Subgroup G)
    (X : SmoothRep.{max v w} A H) :
    (cIndFunctor A H).obj X = SmoothRep.of (V := X.obj.ρ.compactInduction.toSubmodule)
      X.obj.ρ.compactInduction.toRepresentation := (rfl)

/-- The underlying intertwining map of compact induction is postcomposition by the coefficient
morphism. -/
theorem cIndFunctor_map_hom_hom {A : Type u} [Ring A] {H : Subgroup G}
    {X Y : SmoothRep.{max v w} A H} (f : X ⟶ Y) :
    ((cIndFunctor A H).map f).hom.hom = Representation.compactInductionMap f.hom.hom := (rfl)

/-- Compact induction preserves addition of morphisms over a ring. -/
instance additive_cIndFunctor (A : Type u) [Ring A] (H : Subgroup G) :
    (cIndFunctor.{u, v, w} A H).Additive where
  map_add {_ _ f k} := by
    have h : (f + k).hom = f.hom + k.hom := (SmoothRep.ι A H).map_add
    apply (SmoothRep.ι A G).map_injective
    rw [(SmoothRep.ι A G).map_add (f := (cIndFunctor A H).map f) (g := (cIndFunctor A H).map k)]
    apply Rep.hom_ext
    simp only [ObjectProperty.ι_map, Rep.add_hom]
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext g
    simp [h, Rep.add_hom]

/-- Compact induction is linear over a commutative coefficient ring. -/
instance linear_cIndFunctor (A : Type u) [CommRing A] (H : Subgroup G) :
    (cIndFunctor.{u, v, w} A H).Linear A where
  map_smul f r := by
    have h : (r • f).hom = r • f.hom := (SmoothRep.ι A H).map_smul r f
    apply (SmoothRep.ι A G).map_injective
    rw [(SmoothRep.ι A G).map_smul r ((cIndFunctor A H).map f)]
    apply Rep.hom_ext
    simp only [ObjectProperty.ι_map, Rep.smul_hom]
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext g
    simp [h, Rep.smul_hom]

end TauCeti.SmoothRep
