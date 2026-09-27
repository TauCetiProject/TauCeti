/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Augmentation
public import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# The splitting module of a degree-two cohomology class

For a representation `A` of a finite group `G` and a class `u ∈ H²(G, A)`, this file
constructs the **splitting module** `A(u)`. Its underlying module is `I_G × A`, where `I_G` is
the augmentation ideal. A cocycle representing `u` twists the diagonal action on this product.
There is a short exact sequence

`0 → A → A(u) → I_G → 0`,

and the image of `u` in `H²(G, A(u))` is zero. This is the second dimension shift in Tate's
cup-product criterion: once the hypotheses of that criterion show that `A(u)` has vanishing
cohomology in two consecutive degrees for every subgroup, Tate's cohomological triviality
criterion makes it acyclic in every Tate degree.

The construction follows J. S. Milne, *Class Field Theory*, Chapter II, proof of Theorem 3.11.
It is adapted to Mathlib's `Rep` and low-degree cohomology API from
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`, file
`ClassFieldTheory/Cohomology/SplittingModule.lean` (Apache-2.0).

## Main definitions

* `Rep.h2Representative`: a chosen two-cocycle representing a class in `H²`.
* `Rep.splittingModule`: the splitting module of a degree-two class.
* `Rep.splittingModuleSES`: its short exact sequence with the augmentation ideal.

## Main results

* `Rep.splittingModuleSES_shortExact`, `Rep.splittingModuleSES_res_shortExact`: the
  splitting-module sequence is short exact, also after restriction.
* `Rep.map_splittingModuleIncl_eq_zero`: the defining class maps to zero in the splitting
  module's second cohomology.
-/

public noncomputable section

universe u

open CategoryTheory Limits BigOperators

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- A chosen two-cocycle representing `u ∈ H²(G, A)`. -/
def h2Representative (A : Rep k G) (u : groupCohomology A 2) :
    groupCohomology.cocycles₂ A :=
  Classical.choose ((ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance u)

/-- The chosen two-cocycle represents the original second-cohomology class. -/
@[simp]
theorem H2π_h2Representative (A : Rep k G) (u : groupCohomology A 2) :
    groupCohomology.H2π A (h2Representative A u) = u :=
  Classical.choose_spec
    ((ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance u)

variable [Finite G]
/-- A finite enumeration of `G`, used only to write the coefficient sums in the construction. -/
local instance splittingModuleFintype : Fintype G := Fintype.ofFinite G
variable (A : Rep k G) (u : groupCohomology A 2)

/-- The linear correction term contributed by a cocycle to the action on its splitting module. -/
def splittingTwist (g : G) : augmentationIdeal k G →ₗ[k] A :=
  let L : (G →₀ k) →ₗ[k] A :=
    (Finsupp.lsum k) fun h ↦
      LinearMap.toSpanSingleton k A (h2Representative A u (g, h))
  let coeffs : augmentationIdeal k G →ₗ[k] (G →₀ k) :=
    { toFun := fun x ↦ ((augmentationι k G).hom x).coeff
      map_add' := by simp
      map_smul' := by simp }
  L.comp coeffs

/-- The correction term is the coefficientwise pairing with the chosen cocycle representative. -/
theorem splittingTwist_apply (g : G) (x : augmentationIdeal k G) :
    splittingTwist A u g x =
      ∑ h : G, ((augmentationι k G).hom x).coeff h • h2Representative A u (g, h) := by
  simp [splittingTwist, Finsupp.sum_fintype]

/-- The correction term at the identity is zero. -/
@[simp]
theorem splittingTwist_one : splittingTwist A u 1 = 0 := by
  ext x
  rw [splittingTwist_apply]
  simp only [groupCohomology.cocycles₂_map_one_fst]
  rw [← Finset.sum_smul, TauCeti.AugmentationIdeal.sum_coeff_augmentationι, zero_smul,
    LinearMap.zero_apply]

/-- The cocycle identity is precisely the identity needed for the twisted maps to form a group
action on the splitting module. -/
theorem splittingTwist_mul (g₁ g₂ : G) (x : augmentationIdeal k G) :
    splittingTwist A u (g₁ * g₂) x =
      A.ρ g₁ (splittingTwist A u g₂ x) +
        splittingTwist A u g₁ ((augmentationIdeal k G).ρ g₂ x) := by
  rw [splittingTwist_apply, splittingTwist_apply, splittingTwist_apply]
  have hcocycle (a b c : G) :=
    eq_sub_iff_add_eq.mpr
      ((groupCohomology.mem_cocycles₂_iff (h2Representative A u)).mp
        (h2Representative A u).2 a b c)
  simp only [hcocycle, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, map_sum, map_smul]
  rw [← Finset.sum_smul, TauCeti.AugmentationIdeal.sum_coeff_augmentationι, zero_smul,
    sub_zero, add_right_inj]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft g₂)]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [hom_comm_apply]
  simp

/-- The representation on `I_G × A` twisted by a two-cocycle representing `u`.

For `g : G`, the second coordinate of `g • (x, a)` is
`g • a + ∑_h x_h • c(g,h)`, where `c` is the chosen representative of `u`. -/
@[expose]
def splittingModuleRepresentation :
    Representation k G (augmentationIdeal k G × A) where
  toFun g :=
    { toFun x :=
        ((augmentationIdeal k G).ρ g x.1,
          A.ρ g x.2 + splittingTwist A u g x.1)
      map_add' x y := by ext <;> simp [add_add_add_comm]
      map_smul' r x := by ext <;> simp }
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simp
    · simp
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simp
    · simp [splittingTwist_mul, add_assoc]

/-- The **splitting module** `A(u)` of a class `u ∈ H²(G, A)`. Its underlying module is
`I_G × A`; the action is twisted by a chosen cocycle representing `u`. -/
@[expose]
def splittingModule : Rep k G :=
  Rep.of (splittingModuleRepresentation A u)

/-- The action on the splitting module, in terms of the chosen cocycle representative. -/
theorem splittingModule_ρ_apply (g : G) (x : splittingModule A u) :
    (splittingModule A u).ρ g x =
      ((augmentationIdeal k G).ρ g x.1,
        A.ρ g x.2 + splittingTwist A u g x.1) :=
  (rfl)

/-- The inclusion `A → A(u)` into the second factor of the splitting module. -/
@[expose]
def splittingModuleIncl : A ⟶ splittingModule A u :=
  ofHom ⟨LinearMap.inr k (augmentationIdeal k G) A, fun g ↦ by
    ext a
    · change 0 = (augmentationIdeal k G).ρ g 0
      simp
    · change A.ρ g a = A.ρ g a + splittingTwist A u g 0
      simp⟩

/-- The inclusion into the splitting module sends `a` to `(0,a)`. -/
@[simp]
theorem splittingModuleIncl_apply (a : A) : splittingModuleIncl A u a = (0, a) :=
  (rfl)

/-- The projection `A(u) → I_G` from the splitting module to the augmentation ideal. -/
@[expose]
def splittingModuleProj : splittingModule A u ⟶ augmentationIdeal k G :=
  ofHom ⟨LinearMap.fst k (augmentationIdeal k G) A, fun _ ↦ rfl⟩

/-- The projection from the splitting module returns its first coordinate. -/
@[simp]
theorem splittingModuleProj_apply (x : splittingModule A u) :
    splittingModuleProj A u x = x.1 :=
  (rfl)

/-- The short complex `A → A(u) → I_G` associated to the splitting module. -/
@[expose]
def splittingModuleSES : ShortComplex (Rep k G) :=
  { X₁ := A
    X₂ := splittingModule A u
    X₃ := augmentationIdeal k G
    f := splittingModuleIncl A u
    g := splittingModuleProj A u
    zero := by ext; rfl }

/-- The splitting-module sequence `0 → A → A(u) → I_G → 0` is short exact. -/
theorem splittingModuleSES_shortExact : (splittingModuleSES A u).ShortExact := by
  refine
    { exact := by
        change
          (ShortComplex.mk (splittingModuleIncl A u) (splittingModuleProj A u)
            (by ext; rfl)).Exact
        rw [Rep.exact_iff_function_exact]
        exact Function.Exact.inr_fst
      mono_f := (Rep.mono_iff_injective _).2 LinearMap.inr_injective
      epi_g := (Rep.epi_iff_surjective _).2 LinearMap.fst_surjective }

/-- The splitting-module sequence stays short exact after restriction along any monoid
homomorphism `f : H →* G`. -/
theorem splittingModuleSES_res_shortExact {H : Type*} [Monoid H] (f : H →* G) :
    ((splittingModuleSES A u).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (splittingModuleSES_shortExact A u)

/-- The one-cochain `g ↦ ([g]-[1], g • c(1,1))` in the splitting module. Its coboundary is
the image of the chosen representative `c` of `u`. -/
def splittingModuleCochain (g : G) : splittingModule A u :=
  (TauCeti.AugmentationIdeal.singleSub k G 1 g,
    A.ρ g (h2Representative A u (1, 1)))

/-- The coboundary of `splittingModuleCochain` is the image of the chosen cocycle representative
under the inclusion `A → A(u)`. -/
theorem splittingModuleCochain_coboundary (g h : G) :
    (splittingModule A u).ρ g (splittingModuleCochain A u h) -
        splittingModuleCochain A u (g * h) + splittingModuleCochain A u g =
      splittingModuleIncl A u (h2Representative A u (g, h)) := by
  rw [splittingModule_ρ_apply, splittingModuleCochain, splittingModuleCochain,
    splittingModuleCochain, splittingModuleIncl_apply]
  change
    (((((augmentationIdeal k G).ρ g) (TauCeti.AugmentationIdeal.singleSub k G 1 h),
          A.ρ g (A.ρ h (h2Representative A u (1, 1))) +
            splittingTwist A u g (TauCeti.AugmentationIdeal.singleSub k G 1 h)) -
        (TauCeti.AugmentationIdeal.singleSub k G 1 (g * h),
          A.ρ (g * h) (h2Representative A u (1, 1))) +
        (TauCeti.AugmentationIdeal.singleSub k G 1 g,
          A.ρ g (h2Representative A u (1, 1)))) :
      augmentationIdeal k G × A) = (0, h2Representative A u (g, h))
  apply Prod.ext
  · rw [Prod.fst_add, Prod.fst_sub, TauCeti.AugmentationIdeal.ρ_singleSub]
    abel_nf
    simp
  · simp only [Prod.snd_sub, Prod.snd_add, map_mul, Module.End.mul_apply,
      add_sub_cancel_left, splittingTwist_apply]
    rw [TauCeti.AugmentationIdeal.ι_singleSub]
    simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, Finsupp.coe_sub,
      Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    have hsum (y : G) :
        ∑ x : G, (Finsupp.single y (1 : k)) x • h2Representative A u (g, x) =
          h2Representative A u (g, y) := by
      classical
      rw [Finset.sum_eq_single y]
      · simp
      · intro x _ hxy
        simp [hxy]
      · simp
    rw [hsum h, hsum 1]
    have hone : h2Representative A u (g, 1) =
        A.ρ g (h2Representative A u (1, 1)) := by
      simpa [add_comm] using
        (groupCohomology.mem_cocycles₂_iff (h2Representative A u)).mp
          (h2Representative A u).2 g 1 1
    simp [hone]

/-- The chosen representative of `u` becomes a coboundary after mapping it into the splitting
module. -/
theorem h2Representative_mem_coboundaries :
    (splittingModuleIncl A u) ∘ (h2Representative A u) ∈
      groupCohomology.coboundaries₂ (splittingModule A u) := by
  refine ⟨splittingModuleCochain A u, ?_⟩
  ext g
  exact splittingModuleCochain_coboundary A u g.1 g.2

/-- The defining class `u` maps to zero in `H²(G, A(u))`. -/
@[simp]
theorem map_splittingModuleIncl_eq_zero :
    groupCohomology.map (MonoidHom.id G) (splittingModuleIncl A u) 2 u = 0 := by
  calc
    _ = groupCohomology.map (MonoidHom.id G) (splittingModuleIncl A u) 2
        (groupCohomology.H2π A (h2Representative A u)) := by
      rw [H2π_h2Representative]
    _ = groupCohomology.H2π (splittingModule A u)
        (groupCohomology.mapCocycles₂ (MonoidHom.id G) (splittingModuleIncl A u)
          (h2Representative A u)) := by
      rw [← ModuleCat.comp_apply, groupCohomology.H2π_comp_map, ModuleCat.comp_apply]
    _ = 0 := by
      rw [groupCohomology.H2π_eq_zero_iff]
      change (splittingModuleIncl A u) ∘ (h2Representative A u) ∈
        groupCohomology.coboundaries₂ (splittingModule A u)
      exact h2Representative_mem_coboundaries A u

end Rep
