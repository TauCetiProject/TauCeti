/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Minimal complexes of modules

A complex over a commutative ring is minimal if every differential takes values in the
Jacobson radical times its target. Over a local ring this is the usual maximal-ideal
criterion for minimal free resolutions. Finiteness and projectivity of the terms are
separate hypotheses, not part of minimality.

A self-map of a minimal complex of finite modules that is homotopic to the identity is
invertible. Consequently a homotopy equivalence between two such complexes is already an
isomorphism of complexes. No boundedness, freeness, or Noetherian hypothesis is needed.
This rigidity allows properties of the actual terms and differentials, such as periodic
tails, to be recovered from minimal representatives in the homotopy category.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 20:
  minimal free resolutions and their uniqueness.
-/

public section

open CategoryTheory

namespace HomologicalComplex

universe u v

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c}

/-- A complex of modules is minimal if each differential has image in the Jacobson
radical of the ring times its target module. -/
def IsMinimal (K : HomologicalComplex (ModuleCat.{v} R) c) : Prop :=
  ∀ i j, LinearMap.range (K.d i j).hom ≤ Ring.jacobson R • (⊤ : Submodule R (K.X j))

/-- The image criterion characterizing minimal complexes. -/
theorem isMinimal_iff : K.IsMinimal ↔
    ∀ i j, LinearMap.range (K.d i j).hom ≤ Ring.jacobson R • (⊤ : Submodule R (K.X j)) :=
  Iff.rfl

/-- Minimality can be checked just on the differentials allowed by the complex shape. -/
theorem isMinimal_iff_of_rel : K.IsMinimal ↔
    ∀ i j, c.Rel i j →
      LinearMap.range (K.d i j).hom ≤ Ring.jacobson R • (⊤ : Submodule R (K.X j)) := by
  refine ⟨fun h i j _ ↦ h i j, fun h i j ↦ ?_⟩
  by_cases hij : c.Rel i j
  · exact h i j hij
  · simp [K.shape i j hij]

/-- Every value of a differential in a minimal complex lies in the radical times its target. -/
theorem IsMinimal.d_apply_mem (hK : K.IsMinimal) (i j : ι) (x : K.X i) :
    (K.d i j).hom x ∈ Ring.jacobson R • (⊤ : Submodule R (K.X j)) :=
  hK i j (LinearMap.mem_range_self _ x)

/-- Over a local ring, minimality is the usual maximal-ideal image criterion. -/
theorem isMinimal_iff_range_le_maximalIdeal_smul [IsLocalRing R] : K.IsMinimal ↔
    ∀ i j, LinearMap.range (K.d i j).hom ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X j)) := by
  rw [isMinimal_iff, IsLocalRing.ringJacobson_eq_maximalIdeal]

/-- Minimality is preserved by isomorphisms of complexes. -/
theorem IsMinimal.of_iso (hK : K.IsMinimal) (e : K ≅ L) : L.IsMinimal := by
  intro i j y hy
  obtain ⟨x, rfl⟩ := hy
  have hm := (Submodule.smul_top_le_comap_smul_top (Ring.jacobson R) (e.hom.f j).hom)
    (hK.d_apply_mem i j ((e.inv.f i).hom x))
  have he := congrArg (fun a : L.X i ⟶ L.X j ↦ a.hom x)
    (e.inv.comm_assoc i j (e.hom.f j))
  simp only [← comp_f, e.inv_hom_id, id_f, Category.comp_id,
    ModuleCat.hom_comp, LinearMap.comp_apply] at he
  rw [← he]
  exact hm

/-- Homotopic maps between minimal complexes agree modulo the radical in every degree. -/
theorem IsMinimal.sub_mem_of_homotopy (hK : K.IsMinimal) (hL : L.IsMinimal)
    {f g : K ⟶ L} (h : Homotopy f g) (i : ι) (x : K.X i) :
    (f.f i).hom x - (g.f i).hom x ∈ Ring.jacobson R • (⊤ : Submodule R (L.X i)) := by
  have hd := hK.d_apply_mem i (c.next i) x
  have hm := (Submodule.smul_top_le_comap_smul_top (Ring.jacobson R)
    (h.hom (c.next i) i).hom) hd
  have hp := hL.d_apply_mem (c.prev i) i ((h.hom i (c.prev i)).hom x)
  have he := congrArg (fun a : K.X i ⟶ L.X i ↦ a.hom x) (h.comm i)
  simp only [dNext, prevD, AddMonoidHom.mk'_apply, ModuleCat.hom_add,
    ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply] at he
  rw [he, add_sub_cancel_right]
  exact Submodule.add_mem _ hm hp

/-- A self-map homotopic to the identity on a minimal complex of finite modules is an
isomorphism. -/
theorem IsMinimal.isIso_of_homotopy_id (hK : K.IsMinimal) [∀ i, Module.Finite R (K.X i)]
    {f : K ⟶ K} (h : Homotopy f (𝟙 K)) : IsIso f := by
  have hsurj (i : ι) : Function.Surjective (f.f i).hom := by
    apply LinearMap.surjective_of_surjective_comp_mkQ _ (Ring.jacobson R) le_rfl
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Ring.jacobson R •
      (⊤ : Submodule R (K.X i))) y
    refine ⟨x, ?_⟩
    apply (Submodule.Quotient.eq _).2
    simpa using hK.sub_mem_of_homotopy hK h i x
  have (i : ι) : IsIso (f.f i) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (OrzechProperty.bijective_of_surjective_endomorphism (f.f i).hom (hsurj i))
  exact Hom.isIso_of_components f

/-- A homotopy equivalence between minimal complexes of finite modules is already an
isomorphism on its forward chain map. -/
theorem IsMinimal.isIso_hom_of_homotopyEquiv (hK : K.IsMinimal) (hL : L.IsMinimal)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Finite R (L.X i)]
    (e : HomotopyEquiv K L) : IsIso e.hom := by
  have := hK.isIso_of_homotopy_id e.homotopyHomInvId
  have := hL.isIso_of_homotopy_id e.homotopyInvHomId
  have : Mono e.hom := mono_of_mono e.hom e.inv
  have : IsSplitEpi e.hom := IsSplitEpi.mk'
    { section_ := inv (e.inv ≫ e.hom) ≫ e.inv
      id := by simp }
  exact isIso_of_mono_of_isSplitEpi e.hom

end HomologicalComplex

namespace ChainComplex

universe u v

/-- A natural-number-indexed chain complex is minimal exactly when each successive
differential has image in the radical times its target. -/
theorem isMinimal_iff_range_d_succ_le {R : Type u} [CommRing R]
    {K : ChainComplex (ModuleCat.{v} R) ℕ} : K.IsMinimal ↔
    ∀ n, LinearMap.range (K.d (n + 1) n).hom ≤
      Ring.jacobson R • (⊤ : Submodule R (K.X n)) := by
  rw [HomologicalComplex.isMinimal_iff_of_rel]
  exact ⟨fun h n ↦ h (n + 1) n rfl, fun h i j hij ↦ by
    obtain rfl := hij
    exact h j⟩

/-- Over a local ring, a natural-number-indexed chain complex is minimal exactly when each
successive differential has image in the maximal ideal times its target. -/
theorem isMinimal_iff_range_d_succ_le_maximalIdeal_smul {R : Type u} [CommRing R]
    [IsLocalRing R] {K : ChainComplex (ModuleCat.{v} R) ℕ} : K.IsMinimal ↔
    ∀ n, LinearMap.range (K.d (n + 1) n).hom ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X n)) := by
  rw [isMinimal_iff_range_d_succ_le, IsLocalRing.ringJacobson_eq_maximalIdeal]

end ChainComplex
