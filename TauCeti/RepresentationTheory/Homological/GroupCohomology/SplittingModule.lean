/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.Augmentation
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# The splitting module of a degree-two cohomology class

For a representation `A` of a group `G` and a class `u ∈ H²(G, A)`, this file
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

* `Rep.splittingModule`: the splitting module of a degree-two class.
* `Rep.splittingModuleSES`: its short exact sequence with the augmentation ideal.

## Main results

* `Rep.splittingModuleSES_shortExact`, `Rep.splittingModuleSES_res_shortExact`: the
  splitting-module sequence is short exact, also after restriction.
* `Rep.map_splittingModuleIncl_res_eq_zero`: after restriction along any group homomorphism, the
  defining class maps to zero in the splitting module's second cohomology.
-/

public noncomputable section

universe u

open CategoryTheory Limits BigOperators

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]
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
      ((augmentationι k G).hom x).coeff.sum fun h a ↦
        a • h2Representative A u (g, h) := by
  simp only [splittingTwist, LinearMap.comp_apply, Finsupp.lsum_apply]
  exact Finsupp.sum_congr fun _ _ ↦ rfl

/-- The correction term at the identity is zero. -/
@[simp]
theorem splittingTwist_one : splittingTwist A u 1 = 0 := by
  ext x
  rw [splittingTwist_apply]
  simp only [groupCohomology.cocycles₂_map_one_fst]
  rw [Finsupp.sum, ← Finset.sum_smul]
  have hsum := TauCeti.AugmentationIdeal.sum_coeff_augmentationι k G x
  rw [Finsupp.sum] at hsum
  rw [hsum, zero_smul, LinearMap.zero_apply]

private theorem coeff_splitting_action (g : G) (x : augmentationIdeal k G) :
    ((augmentationι k G).hom ((augmentationIdeal k G).ρ g x)).coeff =
      Finsupp.equivMapDomain (Equiv.mulLeft g) ((augmentationι k G).hom x).coeff := by
  ext h
  rw [hom_comm_apply]
  simp [Finsupp.equivMapDomain_apply, Representation.coeff_ofMulAction]

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
  simp only [hcocycle, smul_sub, smul_add, Finsupp.sum_sub, Finsupp.sum_add,
    map_finsuppSum, map_smul]
  have hconst :
      ((augmentationι k G).hom x).coeff.sum
          (fun _ a ↦ a • h2Representative A u (g₁, g₂)) = 0 := by
    rw [Finsupp.sum, ← Finset.sum_smul]
    have hsum := TauCeti.AugmentationIdeal.sum_coeff_augmentationι k G x
    rw [Finsupp.sum] at hsum
    rw [hsum, zero_smul]
  rw [hconst, sub_zero, add_right_inj, coeff_splitting_action,
    Finsupp.sum_equivMapDomain]
  exact Finsupp.sum_congr fun _ _ ↦ rfl

/-- The **splitting module** `A(u)` of a class `u ∈ H²(G, A)`. Its underlying module is
linearly equivalent to `I_G × A`; the action is twisted by a chosen cocycle representing `u`. -/
def splittingModule : Rep k G :=
  Rep.of
    { toFun g :=
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
        · simp [splittingTwist_mul, add_assoc] }

/-- The underlying linear equivalence from the splitting module to `I_G × A`. -/
def splittingModuleEquiv : splittingModule A u ≃ₗ[k] augmentationIdeal k G × A :=
  LinearEquiv.refl k (augmentationIdeal k G × A)

/-- Construct an element of the splitting module from its augmentation-ideal and coefficient
coordinates. -/
def splittingModuleMk (x : augmentationIdeal k G) (a : A) : splittingModule A u :=
  (splittingModuleEquiv A u).symm (x, a)

/-- The coordinates of an element constructed by `splittingModuleMk`. -/
@[simp]
theorem splittingModuleEquiv_mk (x : augmentationIdeal k G) (a : A) :
    splittingModuleEquiv A u (splittingModuleMk A u x a) = (x, a) := by
  simp [splittingModuleMk]

/-- The action on the splitting module, transported to `I_G × A`. -/
@[simp]
theorem splittingModuleEquiv_ρ_apply (g : G) (x : splittingModule A u) :
    splittingModuleEquiv A u ((splittingModule A u).ρ g x) =
      ((augmentationIdeal k G).ρ g (splittingModuleEquiv A u x).1,
        A.ρ g (splittingModuleEquiv A u x).2 +
          splittingTwist A u g (splittingModuleEquiv A u x).1) :=
  (rfl)

/-- The inclusion `A → A(u)` into the second factor of the splitting module. -/
def splittingModuleIncl : A ⟶ splittingModule A u :=
  ofHom ⟨LinearMap.inr k (augmentationIdeal k G) A, fun g ↦ by
    ext a <;> simp⟩

/-- Under `splittingModuleEquiv`, the inclusion sends `a` to `(0, a)`. -/
@[simp]
theorem splittingModuleEquiv_incl_apply (a : A) :
    splittingModuleEquiv A u (splittingModuleIncl A u a) = (0, a) :=
  (rfl)

/-- The projection `A(u) → I_G` from the splitting module to the augmentation ideal. -/
def splittingModuleProj : splittingModule A u ⟶ augmentationIdeal k G :=
  ofHom ⟨LinearMap.fst k (augmentationIdeal k G) A, fun _ ↦ rfl⟩

/-- The projection from the splitting module returns the first transported coordinate. -/
@[simp]
theorem splittingModuleProj_apply (x : splittingModule A u) :
    splittingModuleProj A u x = (splittingModuleEquiv A u x).1 :=
  (rfl)

/-- The inclusion of `A` followed by the projection to `I_G` is zero. -/
@[reassoc (attr := simp)]
theorem splittingModuleIncl_comp_splittingModuleProj :
    splittingModuleIncl A u ≫ splittingModuleProj A u = 0 := by
  ext; rfl

/-- The short complex `A → A(u) → I_G` associated to the splitting module. -/
def splittingModuleSES : ShortComplex (Rep k G) :=
  { X₁ := A
    X₂ := splittingModule A u
    X₃ := augmentationIdeal k G
    f := splittingModuleIncl A u
    g := splittingModuleProj A u
    zero := by ext; rfl }

/-- The splitting-module sequence has maps the inclusion of `A` and the projection to `I_G`. -/
theorem splittingModuleSES_def :
    splittingModuleSES A u =
      ShortComplex.mk (splittingModuleIncl A u) (splittingModuleProj A u)
        (splittingModuleIncl_comp_splittingModuleProj A u) :=
  (rfl)

/-- The left object of the splitting-module sequence is the original representation. -/
@[simp]
theorem splittingModuleSES_X₁ : (splittingModuleSES A u).X₁ = A := (rfl)

/-- The middle object of the splitting-module sequence is the splitting module. -/
@[simp]
theorem splittingModuleSES_X₂ : (splittingModuleSES A u).X₂ = splittingModule A u := (rfl)

/-- The right object of the splitting-module sequence is the augmentation ideal. -/
@[simp]
theorem splittingModuleSES_X₃ :
    (splittingModuleSES A u).X₃ = augmentationIdeal k G := (rfl)

/-- The first map of the splitting-module sequence is the inclusion into the second factor. -/
@[simp]
theorem splittingModuleSES_f :
    HEq (splittingModuleSES A u).f (splittingModuleIncl A u) := (HEq.rfl)

/-- The second map of the splitting-module sequence is projection onto the first factor. -/
@[simp]
theorem splittingModuleSES_g :
    HEq (splittingModuleSES A u).g (splittingModuleProj A u) := (HEq.rfl)

/-- The splitting-module sequence `0 → A → A(u) → I_G → 0` is short exact. -/
theorem splittingModuleSES_shortExact : (splittingModuleSES A u).ShortExact := by
  refine
    { exact := by
        -- Normalize the opaque short complex before exposing its underlying functions.
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
  splittingModuleMk A u (TauCeti.AugmentationIdeal.singleSub k G 1 g)
    (A.ρ g (h2Representative A u (1, 1)))

/-- The coboundary of `splittingModuleCochain` is the image of the chosen cocycle representative
under the inclusion `A → A(u)`. -/
theorem splittingModuleCochain_coboundary (g h : G) :
    (splittingModule A u).ρ g (splittingModuleCochain A u h) -
        splittingModuleCochain A u (g * h) + splittingModuleCochain A u g =
      splittingModuleIncl A u (h2Representative A u (g, h)) := by
  apply (splittingModuleEquiv A u).injective
  simp only [map_add, map_sub, splittingModuleEquiv_ρ_apply, splittingModuleCochain,
    splittingModuleEquiv_mk, splittingModuleEquiv_incl_apply]
  apply Prod.ext
  · rw [Prod.fst_add, Prod.fst_sub, TauCeti.AugmentationIdeal.ρ_singleSub]
    abel_nf
    simp
  · simp only [Prod.snd_sub, Prod.snd_add, map_mul, Module.End.mul_apply,
      add_sub_cancel_left, splittingTwist_apply]
    rw [TauCeti.AugmentationIdeal.ι_singleSub]
    simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single]
    rw [Finsupp.sum_sub_index (fun _ _ _ ↦ sub_smul _ _ _),
      Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp
    have hone : h2Representative A u (g, 1) =
        A.ρ g (h2Representative A u (1, 1)) := by
      simpa [add_comm] using
        (groupCohomology.mem_cocycles₂_iff (h2Representative A u)).mp
          (h2Representative A u).2 g 1 1
    simp [hone]

/-- The composite of the chosen representative of `u` with the splitting-module inclusion is a
coboundary. -/
theorem splittingModuleIncl_comp_h2Representative_mem_coboundaries :
    (splittingModuleIncl A u) ∘ (h2Representative A u) ∈
      groupCohomology.coboundaries₂ (splittingModule A u) := by
  refine ⟨splittingModuleCochain A u, ?_⟩
  ext g
  exact splittingModuleCochain_coboundary A u g.1 g.2

/-- After restriction along any group homomorphism, the defining class `u` maps to zero in the
second cohomology of the restricted splitting module. -/
@[simp]
theorem map_splittingModuleIncl_res_eq_zero {H : Type u} [Group H] (f : H →* G) :
    groupCohomology.map f ((resFunctor f).map (splittingModuleIncl A u)) 2 u = 0 := by
  calc
    _ = groupCohomology.map f ((resFunctor f).map (splittingModuleIncl A u)) 2
        (groupCohomology.H2π A (h2Representative A u)) := by
      rw [H2π_h2Representative]
    _ = groupCohomology.H2π (res f (splittingModule A u))
        (groupCohomology.mapCocycles₂ f ((resFunctor f).map (splittingModuleIncl A u))
          (h2Representative A u)) := by
      rw [← ModuleCat.comp_apply, groupCohomology.H2π_comp_map, ModuleCat.comp_apply]
    _ = 0 := by
      rw [groupCohomology.H2π_eq_zero_iff]
      refine ⟨fun g ↦ splittingModuleCochain A u (f g), ?_⟩
      ext g
      -- Isolate the definitional transports through restriction and `mapCocycles₂`.
      have resAction_apply :
          (res f (splittingModule A u)).ρ g.1 (splittingModuleCochain A u (f g.2)) =
            (splittingModule A u).ρ (f g.1) (splittingModuleCochain A u (f g.2)) := rfl
      have mapCocycles₂_apply :
          groupCohomology.mapCocycles₂ f ((resFunctor f).map (splittingModuleIncl A u))
              (h2Representative A u) g =
            splittingModuleIncl A u (h2Representative A u (f g.1, f g.2)) := rfl
      rw [groupCohomology.d₁₂_hom_apply, resAction_apply, mapCocycles₂_apply, map_mul]
      exact splittingModuleCochain_coboundary A u (f g.1) (f g.2)

/-- The defining class `u` maps to zero in `H²(G, A(u))`. -/
@[simp]
theorem map_splittingModuleIncl_eq_zero :
    groupCohomology.map (MonoidHom.id G) (splittingModuleIncl A u) 2 u = 0 := by
  exact map_splittingModuleIncl_res_eq_zero A u (MonoidHom.id G)

end Rep
