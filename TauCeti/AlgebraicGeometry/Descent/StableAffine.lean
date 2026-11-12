/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Open
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.ProjectiveNorm
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.AffineScheme.FiniteSet

/-!
# Stable affine neighborhoods for finite flat descent

Finite descent orbits contained in affine opens admit stable affine neighborhoods. Prime
avoidance first shrinks an affine neighborhood around the whole orbit. The projective norm
then gives an affine open on which every point's entire orbit remains in that basic open.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental*, Exposé VIII, §7.
* The Stacks Project, descent of schemes with affine neighborhoods of finite sets.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'} (D : DescentDatum p X)

private theorem lift_comp_act {T : Scheme.{u}} (s : T ⟶ S')
    (z : T ⟶ pullback p (X.hom ≫ p))
    (h : s ≫ p = z ≫ pullback.fst p (X.hom ≫ p) ≫ p) :
    pullback.lift s (z ≫ D.act) (by simpa using h) ≫ D.act =
      pullback.lift s (z ≫ pullback.snd p (X.hom ≫ p))
        (by simpa only [Category.assoc, ← pullback.condition] using h) ≫ D.act := by
  have key := pullback.lift s z h ≫= D.act_assoc
  convert key using 1 <;> simp only [← Category.assoc] <;>
    congr 1 <;> apply pullback.hom_ext <;> simp

private theorem exists_snd_eq_act_eq (x : X.left) :
    ∃ z, pullback.snd p (X.hom ≫ p) z = x ∧ D.act z = x := by
  refine ⟨pullback.lift X.hom (𝟙 X.left) (by simp) x, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    rfl
  · rw [← Scheme.Hom.comp_apply, lift_act]
    rfl

private theorem exists_reverse (z : (pullback p (X.hom ≫ p) : Scheme.{u})) :
    ∃ w, pullback.snd p (X.hom ≫ p) w = D.act z ∧
      D.act w = pullback.snd p (X.hom ≫ p) z := by
  let s := pullback.snd p (X.hom ≫ p) ≫ X.hom
  have h : s ≫ p = (𝟙 _) ≫ pullback.fst p (X.hom ≫ p) ≫ p := by
    simpa [s] using (pullback.condition (f := p) (g := X.hom ≫ p)).symm
  refine ⟨pullback.lift s ((𝟙 _) ≫ D.act) (by simpa using h) z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    simp
  · rw [← Scheme.Hom.comp_apply, D.lift_comp_act s (𝟙 _) h]
    have heq : pullback.lift (f := p) (g := X.hom ≫ p) s ((𝟙 _) ≫ pullback.snd p (X.hom ≫ p))
        (by simpa only [Category.assoc, ← pullback.condition] using h) =
        pullback.snd p (X.hom ≫ p) ≫
          pullback.lift X.hom (𝟙 X.left) (by simp) := by
      apply pullback.hom_ext <;> simp [s]
    rw [heq, Category.assoc, D.lift_act, Category.comp_id]

private theorem exists_comp (a b : (pullback p (X.hom ≫ p) : Scheme.{u}))
    (hab : D.act a = pullback.snd p (X.hom ≫ p) b) :
    ∃ c, pullback.snd p (X.hom ≫ p) c = pullback.snd p (X.hom ≫ p) a ∧
      D.act c = D.act b := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  let f := pullback.fst D.act (pullback.snd p (X.hom ≫ p))
  let g := pullback.snd D.act (pullback.snd p (X.hom ≫ p))
  have h : (g ≫ pullback.fst p (X.hom ≫ p)) ≫ p =
      f ≫ pullback.fst p (X.hom ≫ p) ≫ p := by
    calc
      _ = g ≫ pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p := by
        simp only [Category.assoc, pullback.condition]
      _ = f ≫ D.act ≫ X.hom ≫ p := by
        simpa only [Category.assoc] using
          (pullback.condition_assoc (f := D.act)
            (g := pullback.snd p (X.hom ≫ p)) (X.hom ≫ p)).symm
      _ = _ := by rw [D.act_hom_assoc]
  refine ⟨pullback.lift (g ≫ pullback.fst p (X.hom ≫ p))
    (f ≫ pullback.snd p (X.hom ≫ p))
    (by simpa only [Category.assoc, ← pullback.condition] using h) z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, hz₁]
  · rw [← Scheme.Hom.comp_apply, ← D.lift_comp_act _ f h]
    have heq : pullback.lift (g ≫ pullback.fst p (X.hom ≫ p)) (f ≫ D.act)
        (by simpa using h) = g := by
      apply pullback.hom_ext
      · simp
      · rw [pullback.lift_snd]
        exact pullback.condition
    rw [heq, Scheme.Hom.comp_apply, hz₂]

private theorem isStable_of_forall_mem_iff (U : X.left.Opens) (t : Set X.left)
    (hU : ∀ x, x ∈ U ↔ ∀ z, pullback.snd p (X.hom ≫ p) z = x → D.act z ∈ t) :
    D.IsStable U := by
  have step (z : (pullback p (X.hom ≫ p) : Scheme.{u}))
      (hz : pullback.snd p (X.hom ≫ p) z ∈ U) : D.act z ∈ U := by
    apply (hU _).mpr
    intro w hw
    obtain ⟨c, hc₁, hc₂⟩ := D.exists_comp z w hw.symm
    exact hc₂ ▸ (hU _).mp hz c hc₁
  refine isStable_iff.mpr fun z ↦ ⟨?_, step z⟩
  intro hz
  obtain ⟨w, hw₁, hw₂⟩ := D.exists_reverse z
  rw [← hw₂]
  exact step w (hw₁.symm ▸ hz)

private theorem isOpen_setOf_forall_act_mem [IsFinite p] {t : Set X.left} (ht : IsOpen t) :
    IsOpen {x | ∀ z, pullback.snd p (X.hom ≫ p) z = x → D.act z ∈ t} := by
  have heq : {x | ∀ z, pullback.snd p (X.hom ≫ p) z = x → D.act z ∈ t} =
      (pullback.snd p (X.hom ≫ p) '' (D.act ⁻¹' tᶜ))ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage,
      not_exists, not_and]
    exact forall_congr' fun z ↦
      ⟨fun h hz hx ↦ hz (h hx), fun h hx ↦ by_contra (h · hx)⟩
  rw [heq, isOpen_compl_iff]
  exact (pullback.snd p (X.hom ≫ p)).isClosedMap _
    (ht.isClosed_compl.preimage D.act.continuous)

/-- If every finite subset of a fibre over `S` is contained in an affine open, then every
point of a stable open has a stable affine neighborhood inside it, for finite flat descent
locally of finite presentation. Surjectivity is unnecessary for this local construction. -/
theorem exists_isStable_isAffineOpen_le [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    (hfinite : ∀ (s : S) (t : Set X.left), t.Finite →
      (∀ x ∈ t, (X.hom ≫ p) x = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ t ⊆ U)
    {V : X.left.Opens} (hV : D.IsStable V) {x : X.left} (hx : x ∈ V) :
    ∃ U : X.left.Opens, x ∈ U ∧ U ≤ V ∧ D.IsStable U ∧ IsAffineOpen U := by
  let f := pullback.snd p (X.hom ≫ p)
  let orbit := D.act '' (f ⁻¹' {x})
  have horbit : orbit.Finite := (f.finite_preimage_singleton x).image _
  have hbase (z : (pullback p (X.hom ≫ p) : Scheme.{u})) :
      (X.hom ≫ p) (D.act z) = (X.hom ≫ p) (f z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun g ↦ g z) D.act_comp_hom_comp
  obtain ⟨A, hA, horbitA⟩ := hfinite ((X.hom ≫ p) x) orbit horbit (by
    rintro _ ⟨z, hz, rfl⟩
    rw [hbase, Set.mem_singleton_iff.mp hz])
  let W : X.left.Opens := ⟨_, D.isOpen_setOf_forall_act_mem (A ⊓ V).isOpen⟩
  have hWA : W ≤ A ⊓ V := fun y hy ↦ by
    obtain ⟨z, hz₁, hz₂⟩ := D.exists_snd_eq_act_eq y
    exact hz₂ ▸ hy z hz₁
  have horbitW : orbit ⊆ W := by
    rintro _ ⟨a, ha, rfl⟩ b hb
    obtain ⟨c, hc₁, hc₂⟩ := D.exists_comp a b hb.symm
    have hmem : D.act b ∈ orbit := ⟨c, hc₁.trans ha, hc₂⟩
    refine ⟨horbitA hmem, ?_⟩
    obtain ⟨z, hz, hzb⟩ := hmem
    rw [← hzb]
    apply (isStable_iff.mp hV z).mpr
    rw [Set.mem_singleton_iff.mp hz]
    exact hx
  obtain ⟨r, horbitr, hrW⟩ := hA.exists_basicOpen_le_of_finite
    (O := W ⊓ A) inf_le_right horbit (Set.subset_inter horbitW horbitA)
  let B := X.left.basicOpen r
  have hB : IsAffineOpen B := hA.basicOpen r
  have hBV : B ≤ V := hrW.trans (inf_le_left.trans (hWA.trans inf_le_right))
  have hmap : f ⁻¹ᵁ B ≤ D.act ⁻¹ᵁ A := fun z hz ↦
    ((hrW hz).1 z rfl).1
  let s := D.act.appLE A (f ⁻¹ᵁ B) hmap r
  let := (f.app B).hom.toAlgebra
  have : Module.Finite Γ(X.left, B) Γ(pullback p (X.hom ≫ p), f ⁻¹ᵁ B) := f.finite_app B hB
  have hproj := f.projective_app ⟨B, hB⟩
  let := hproj
  let n := Algebra.projectiveNorm Γ(X.left, B) s
  have key (y : X.left) : y ∈ X.left.basicOpen n ↔
      ∀ z, f z = y → D.act z ∈ B := by
    have hnorm (hy : y ∈ B) := f.mem_basicOpen_projectiveNorm_iff hB hproj s hy
    refine ⟨fun hy z hz ↦ ?_, fun hy ↦ ?_⟩
    · have hm := (hnorm (X.left.basicOpen_le n hy)).mp hy z hz
      rw [Scheme.basicOpen_appLE] at hm
      exact hm.2
    · obtain ⟨z, hz₁, hz₂⟩ := D.exists_snd_eq_act_eq y
      have hyB : y ∈ B := hz₂ ▸ hy z hz₁
      apply (hnorm hyB).mpr
      intro z hz
      rw [Scheme.basicOpen_appLE]
      exact ⟨(Scheme.Hom.mem_preimage (f := f)).mpr (hz.symm ▸ hyB), hy z hz⟩
  exact ⟨X.left.basicOpen n, (key x).mpr fun z hz ↦ horbitr ⟨z, hz, rfl⟩,
    (X.left.basicOpen_le n).trans hBV, D.isStable_of_forall_mem_iff _ _ key, hB.basicOpen n⟩

end TauCeti.DescentDatum
