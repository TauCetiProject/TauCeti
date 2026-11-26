/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Internal
public import TauCeti.RingTheory.Almost.Closed
public import TauCeti.RingTheory.Almost.Projective.Basic

/-!
# Internal projectivity of almost modules

An almost module is almost projective when its internal Hom functor preserves epimorphisms.
The predicate is Mathlib's `CategoryTheory.isInternallyProjective`, which uses internal Hom
rather than ordinary sets of morphisms.
It amounts to lifting each ideal multiple of a morphism through any epimorphism, and equivalently
to factoring every ideal multiple of the identity through the almostification of a free module.
Ordinary projective modules become almost projective after almostification.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, §2.4, Definition 2.4.4, (2.4.8), and
  Lemma 2.4.15.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.Almost.Module

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- Internal Hom sends `f : X → Y` to an epimorphism precisely when each ideal multiple of
every morphism `M → Y` lifts across `f`. -/
theorem epi_alHom_map_iff {M X Y : Module S} (f : X ⟶ Y) :
    Epi ((alHom S M).map f) ↔
      ∀ ε ∈ S.ideal, ∀ g : M ⟶ Y, ∃ h : M ⟶ X, h ≫ f = ε • g := by
  rw [alHom_map, epi_comp_iff_of_epi, epi_comp_iff_of_isIso]
  rw [epi_toAlmost_map_iff, BasicSetup.isAlmostZero_iff]
  constructor
  · intro hf ε hε g
    have h := hf ε hε (Submodule.Quotient.mk g)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    exact h
  · intro hf ε hε g
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hf ε hε g

/-- Almost projectivity is the lifting property for ideal multiples of morphisms. -/
theorem isInternallyProjective_iff_lifting (M : Module S) :
    isInternallyProjective M ↔
      ∀ {X Y : Module S} (f : X ⟶ Y), Epi f →
        ∀ ε ∈ S.ideal, ∀ g : M ⟶ Y, ∃ h : M ⟶ X, h ≫ f = ε • g := by
  rw [isInternallyProjective, ihom_eq_alHom]
  exact ⟨fun _ _ _ f _ ↦ (epi_alHom_map_iff S f).mp (inferInstance),
    fun h ↦ ⟨fun f hf ↦ (epi_alHom_map_iff S f).mpr (h f hf)⟩⟩

/-- The almostification of an ordinary projective module is almost projective. -/
theorem isInternallyProjective_toAlmost (P : ModuleCat.{u} V) [Module.Projective V P] :
    isInternallyProjective ((toAlmost S).obj P) := by
  rw [isInternallyProjective_iff_lifting]
  intro X Y f hf ε hε g
  -- The map on almost elements has almost-zero cokernel. Multiply the adjoint of `g` by `ε`
  -- so it lands in the range, then lift along the surjection onto that range.
  let q := (elements S).map f
  have hq : Epi ((toAlmost S).map q) := by
    apply (epi_comp_iff_of_isIso _ ((adjElements S).counit.app Y)).mp
    have hn : (toAlmost S).map q ≫ (adjElements S).counit.app Y =
        (adjElements S).counit.app X ≫ f := (adjElements S).counit.naturality f
    rw [hn]
    infer_instance
  have hzero := (epi_toAlmost_map_iff S q).mp hq
  let g' := ((adjElements S).homEquiv P Y g).hom
  have hr (x : P) : ε • g' x ∈ LinearMap.range q.hom := by
    have h := hzero.smul_eq_zero hε (Submodule.Quotient.mk (g' x))
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  let k := (ε • g').codRestrict (LinearMap.range q.hom) hr
  obtain ⟨l, hl⟩ := Module.projective_lifting_property q.hom.rangeRestrict k
    q.hom.surjective_rangeRestrict
  let l' : P ⟶ (elements S).obj X := ModuleCat.ofHom l
  refine ⟨((adjElements S).homEquiv P X).symm l', ?_⟩
  have heq : l' ≫ q = ε • ((adjElements S).homEquiv P Y g) := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hl x)
  rw [← (adjElements S).homEquiv_naturality_right_symm]
  rw [heq]
  rw [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp,
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

/-- Almost projectivity is equivalent to factoring every ideal multiple of the identity through
the almostification of a free module. The free rank may be infinite and may depend on the scalar;
compare the finite-rank version in Gabber–Ramero, Lemma 2.4.15. -/
theorem isInternallyProjective_iff_factor (M : Module S) :
    isInternallyProjective M ↔
      ∀ ε ∈ S.ideal, ∃ (I : Type u)
        (u : M ⟶ (toAlmost S).obj (ModuleCat.of V (I →₀ V)))
        (v : (toAlmost S).obj (ModuleCat.of V (I →₀ V)) ⟶ M), u ≫ v = ε • 𝟙 M := by
  classical
  constructor
  · intro h ε hε
    let Q := (elements S).obj M
    let p : ModuleCat.of V (Q →₀ V) ⟶ Q :=
      ModuleCat.ofHom (Finsupp.linearCombination V id)
    have hp : Epi p := (ModuleCat.epi_iff_surjective p).mpr
      (Finsupp.linearCombination_id_surjective V Q)
    let v := (toAlmost S).map p ≫ (adjElements S).counit.app M
    obtain ⟨u, hu⟩ := (isInternallyProjective_iff_lifting S M).mp h v
      (inferInstance) ε hε (𝟙 M)
    exact ⟨Q, u, v, hu⟩
  · intro h
    rw [isInternallyProjective_iff_lifting]
    intro X Y f hf ε hε g
    -- One factor of the scalar passes through a free module and the other lifts across `f`.
    -- Idempotence of the setup ideal assembles the lifts for products into a lift for `ε`.
    refine S.mul_induction_on hε (fun a ha b hb ↦ ?_) fun a b ha hb ↦ ?_
    · obtain ⟨I, u, v, huv⟩ := h b hb
      obtain ⟨l, hl⟩ := (isInternallyProjective_iff_lifting S _).mp
        (isInternallyProjective_toAlmost S (ModuleCat.of V (I →₀ V))) f hf a ha (v ≫ g)
      refine ⟨u ≫ l, ?_⟩
      calc
        (u ≫ l) ≫ f = u ≫ (a • (v ≫ g)) := by rw [Category.assoc, hl]
        _ = a • ((u ≫ v) ≫ g) := by simp [Category.assoc]
        _ = (a * b) • g := by simp [huv, mul_smul]
    · obtain ⟨l₁, hl₁⟩ := ha
      obtain ⟨l₂, hl₂⟩ := hb
      exact ⟨l₁ + l₂, by simp [hl₁, hl₂, add_smul]⟩

/-- In the classical setup almost projectivity is ordinary module projectivity. -/
@[simp]
theorem isInternallyProjective_toAlmost_classical_iff (P : ModuleCat.{u} V) :
    isInternallyProjective ((toAlmost (BasicSetup.classical V)).obj P) ↔
      _root_.Module.Projective V P := by
  constructor
  · intro h
    obtain ⟨I, u, v, huv⟩ :=
      (isInternallyProjective_iff_factor (BasicSetup.classical V) _).mp h 1 (by simp)
    let F := toAlmost (BasicSetup.classical V)
    let u' := F.preimage u
    let v' := F.preimage v
    have hsplit : u' ≫ v' = 𝟙 P := by
      apply F.map_injective
      simpa [u', v'] using huv
    exact _root_.Module.Projective.of_split u'.hom v'.hom
      (congrArg ModuleCat.Hom.hom hsplit)
  · intro h
    exact isInternallyProjective_toAlmost _ P

/-- The finite factorisation criterion for an ordinary module implies internal projectivity
of its almostification. -/
theorem _root_.TauCeti.Almost.BasicSetup.IsAlmostFiniteProjective.isInternallyProjective_toAlmost
    {N : Type u} [AddCommGroup N] [_root_.Module V N] (h : S.IsAlmostFiniteProjective N) :
    isInternallyProjective ((toAlmost S).obj (ModuleCat.of V N)) := by
  classical
  rw [isInternallyProjective_iff_factor]
  intro ε hε
  obtain ⟨n, u, v, huv⟩ := BasicSetup.isAlmostFiniteProjective_iff.mp h ε hε
  let I := ULift.{u} (Fin n)
  let e : (I →₀ V) ≃ₗ[V] (Fin n → V) :=
    (Finsupp.domLCongr Equiv.ulift).trans (Finsupp.linearEquivFunOnFinite V V (Fin n))
  let u' : N →ₗ[V] I →₀ V := e.symm.toLinearMap ∘ₗ u
  let v' : (I →₀ V) →ₗ[V] N := v ∘ₗ e.toLinearMap
  have hcomp : v' ∘ₗ u' = ε • LinearMap.id := by
    ext x
    simpa only [u', v', LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      LinearMap.congr_fun huv x
  refine ⟨I, (toAlmost S).map (ModuleCat.ofHom u'),
    (toAlmost S).map (ModuleCat.ofHom v'), ?_⟩
  rw [← Functor.map_comp]
  have heq : ModuleCat.ofHom u' ≫ ModuleCat.ofHom v' =
      ε • 𝟙 (ModuleCat.of V N) := ModuleCat.hom_ext hcomp
  rw [heq, Functor.map_smul, (toAlmost S).map_id]

end TauCeti.Almost.Module
