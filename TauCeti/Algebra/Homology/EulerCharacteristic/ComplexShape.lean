/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.Algebra.Category.FGModuleCat.Finrank

import TauCeti.Algebra.Category.FGModuleCat.Homology
import TauCeti.Algebra.Homology.EulerCharacteristic.Basic
import TauCeti.Algebra.Homology.EulerCharacteristic.Finite
import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Euler--Poincaré for finitely supported complexes of arbitrary shape

Let `C` be an abelian category, `c : ComplexShape ι` a complex shape equipped with alternating
signs (`ComplexShape.EulerCharSigns`), and `K : HomologicalComplex C c` a complex whose terms
vanish outside a finite set `s : Finset ι`. Suppose `P : ObjectProperty C` contains a zero object
and is closed under kernels and cokernels (for instance, a weak Serre class or a Serre class),
every term `K.X i` for `i ∈ s` lies in `P`, and `v : C → G` is a function into an abelian group
that is additive on short exact sequences whose terms lie in `P`.

This file proves the general Euler--Poincaré identity
(`HomologicalComplex.sum_χ_smul_X_eq_sum_χ_smul_homology`):

```text
∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) = ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i).
```

The argument needs neither closure of `P` under extensions nor any order or direct-sum regrouping
on the index type `ι`. At each index `i`, the two canonical short exact sequences
`0 ⟶ ker g ⟶ X₂ ⟶ coim g ⟶ 0` and `0 ⟶ im f ⟶ ker g ⟶ H ⟶ 0` for `K.sc i` stay inside `P` and
yield `v (K.X i) = v (K.homology i) + v (im (K.d (c.prev i) i)) + v (im (K.d i (c.next i)))`
(`CategoryTheory.ShortComplex.map_X₂_eq_add_image`). Weighting by `c.χ i` and summing over `i ∈ s`,
each relation `c.Rel i j` appears once from `i` with sign `c.χ i` and once from `j` with sign
`c.χ j = -c.χ i`, so all boundary terms cancel pairwise.

Specializing to `P = ⊤` yields the identity for any `TauCeti.AbelianK0.AdditiveInvariant`
(`HomologicalComplex.sum_χ_smul_obj_X_eq_sum_χ_smul_obj_homology`), and specializing to finrank on
finitely generated modules over a Noetherian ring satisfying rank-nullity identifies Mathlib's
`HomologicalComplex.eulerChar` with `HomologicalComplex.homologyEulerChar` for any finitely
supported complex of arbitrary shape
(`HomologicalComplex.eulerChar_eq_homologyEulerChar_of_finset`).

## References

* Stacks Project, Tag 02MO (weak Serre subcategories) and Tag 0754 (characterisation by kernels,
  cokernels and extensions).
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.3 and 1.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

section Additive

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  {G : Type*} [AddCommGroup G] {v : C → G}

/-- A function into an abelian group that is additive on short exact sequences in `P` vanishes on
every zero object, provided `P` contains zero and is closed under isomorphisms. -/
lemma map_eq_zero_of_isZero
    (hv : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      v S.X₂ = v S.X₁ + v S.X₃)
    {Z : C} (hZ : IsZero Z) : v Z = 0 := by
  have hS : (ShortComplex.mk (𝟙 Z) (𝟙 Z) (hZ.eq_of_src _ _)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hZ
      mono_f := inferInstance
      epi_g := inferInstance }
  have hPZ : P Z := P.prop_of_isZero hZ
  exact left_eq_add.mp (hv _ hS hPZ hPZ hPZ)

/-- A function into an abelian group that is additive on short exact sequences in `P` takes the
same value on isomorphic objects in `P`. -/
lemma map_eq_of_iso
    (hv : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      v S.X₂ = v S.X₁ + v S.X₃)
    {X Y : C} (e : X ≅ Y) (hX : P X) : v X = v Y := by
  obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
  let S : ShortComplex C := ShortComplex.mk e.hom (0 : Y ⟶ Z) (by simp)
  have hepi : Epi S.g := ⟨fun _ _ _ ↦ hZ.eq_of_src _ _⟩
  have hExact : S.Exact :=
    (ShortComplex.HomologyData.ofIsColimitCokernelCofork S rfl _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : Y ⟶ Z) comp_zero)
        (by dsimp [S]; infer_instance) hZ)).exact_iff.2 hZ
  have hS : S.ShortExact :=
    { exact := hExact
      mono_f := by dsimp [S]; infer_instance
      epi_g := hepi }
  have h := hv S hS hX (P.prop_of_iso e hX) hPZ
  dsimp [S] at h
  rw [P.map_eq_zero_of_isZero hv hZ, add_zero] at h
  exact h.symm

end Additive

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable def cokernelAbelianImageToKernelIsoHomology (S : ShortComplex C) :
    cokernel S.abelianImageToKernel ≅ S.homology := by
  have hfac :
      kernel.lift S.g S.f S.zero = Abelian.factorThruImage S.f ≫ S.abelianImageToKernel := by
    rw [← cancel_mono (kernel.ι S.g), kernel.lift_ι, Category.assoc,
      S.abelianImageToKernel_comp_kernel_ι, Abelian.image.fac]
  exact (cokernelEpiComp (Abelian.factorThruImage S.f) S.abelianImageToKernel).symm ≪≫
    cokernelIsoOfEq hfac.symm ≪≫ S.homologyIsoCokernelLift.symm

/-- **Short-complex rank--nullity identity for an additive function on a kernel/cokernel-closed
class.** For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` whose terms lie in a class `P` containing zero
and closed under kernels and cokernels, any function `v` additive on short exact sequences in `P`
satisfies `v X₂ = v (H S) + v (im f) + v (im g)`. -/
theorem map_X₂_eq_add_image (S : ShortComplex C) (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G)
    (hv : ∀ T : ShortComplex C, T.ShortExact → P T.X₁ → P T.X₂ → P T.X₃ →
      v T.X₂ = v T.X₁ + v T.X₃)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    v S.X₂ = v S.homology + v (Abelian.image S.f) + v (Abelian.image S.g) := by
  have := P.isClosedUnderIsomorphisms_of_isClosedUnderKernels
  have hK : P (kernel S.g) := P.prop_kernel S.g h₂ h₃
  have hImF : P (Abelian.image S.f) :=
    P.prop_kernel (cokernel.π S.f) h₂ (P.prop_cokernel S.f h₁ h₂)
  have hCoimG : P (Abelian.coimage S.g) := P.prop_cokernel (kernel.ι S.g) hK h₂
  have hCok : P (cokernel S.abelianImageToKernel) :=
    P.prop_cokernel S.abelianImageToKernel hImF hK
  -- Short exact sequence `0 ⟶ ker g ⟶ X₂ ⟶ coim g ⟶ 0`.
  have hS₁ : (ShortComplex.mk (kernel.ι S.g) (cokernel.π (kernel.ι S.g))
      (cokernel.condition _)).ShortExact :=
    ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h₁' : v S.X₂ = v (kernel S.g) + v (Abelian.coimage S.g) := hv _ hS₁ hK h₂ hCoimG
  -- Short exact sequence `0 ⟶ im f ⟶ ker g ⟶ coker(im f ⟶ ker g) ⟶ 0`.
  have hS₂ : (ShortComplex.mk S.abelianImageToKernel (cokernel.π S.abelianImageToKernel)
      (cokernel.condition _)).ShortExact :=
    ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h₂' : v (kernel S.g) = v (Abelian.image S.f) + v (cokernel S.abelianImageToKernel) :=
    hv _ hS₂ hImF hK hCok
  rw [h₁', h₂', P.map_eq_of_iso hv (Abelian.coimageIsoImage S.g) hCoimG,
    P.map_eq_of_iso hv S.cokernelAbelianImageToKernelIsoHomology hCok]
  abel

end CategoryTheory.ShortComplex

namespace HomologicalComplex

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

private lemma isZero_abelianImage_of_eq_zero {X Y : C} {f : X ⟶ Y} (hf : f = 0) :
    IsZero (Abelian.image f) :=
  have := cokernel.π_of_zero hf
  Limits.isZero_kernel_of_mono (cokernel.π f)

private lemma isZero_abelianImage_of_isZero_tgt {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) :
    IsZero (Abelian.image f) :=
  IsZero.of_mono (Abelian.image.ι f) hY

private lemma isZero_abelianImage_of_isZero_src {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    IsZero (Abelian.image f) :=
  isZero_abelianImage_of_eq_zero (hX.eq_of_src f 0)

/-- **Euler--Poincaré for a finitely supported complex of arbitrary shape.** Let `c` be a complex
shape with alternating signs (`ComplexShape.EulerCharSigns`), `K : HomologicalComplex C c` a
complex vanishing outside a finite set `s`, and `P` a property containing zero and closed under
kernels and cokernels such that `K.X i` lies in `P` for every `i ∈ s`. Then for any function
`v : C → G` into an abelian group that is additive on short exact sequences in `P`,

```text
∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) = ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i).
``` -/
theorem sum_χ_smul_X_eq_sum_χ_smul_homology [c.EulerCharSigns]
    (K : HomologicalComplex C c) (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G)
    (hv : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      v S.X₂ = v S.X₁ + v S.X₃)
    (s : Finset ι) (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) (hsP : ∀ i ∈ s, P (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i) := by
  classical
  have := P.isClosedUnderIsomorphisms_of_isClosedUnderKernels
  have hP : ∀ i : ι, P (K.X i) := fun i ↦
    if hi : i ∈ s then hsP i hi else P.prop_of_isZero (hs i hi)
  have hX : ∀ i : ι, v (K.X i) =
      v (K.homology i) + v (Abelian.image (K.d (c.prev i) i)) +
        v (Abelian.image (K.d i (c.next i))) := fun i ↦
    (K.sc i).map_X₂_eq_add_image P v hv (hP _) (hP _) (hP _)
  -- Rewrite the outgoing and incoming boundary terms as sums over `s` indexed by `c.Rel`.
  have hout : ∀ i ∈ s, v (Abelian.image (K.d i (c.next i))) =
      ∑ j ∈ s, if c.Rel i j then v (Abelian.image (K.d i j)) else 0 := by
    intro i _
    by_cases hrel : c.Rel i (c.next i)
    · by_cases hmem : c.next i ∈ s
      · rw [Finset.sum_eq_single (c.next i)]
        · simp [hrel]
        · intro j _ hne
          exact ite_eq_right (fun h ↦ hne (c.next_eq' h).symm)
        · intro h; exact absurd hmem h
      · rw [P.map_eq_zero_of_isZero hv (isZero_abelianImage_of_isZero_tgt _ (hs _ hmem))]
        symm
        refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ hmem ?_
        rwa [c.next_eq' h]
    · rw [P.map_eq_zero_of_isZero hv (isZero_abelianImage_of_eq_zero (K.shape _ _ hrel))]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ hrel ?_
      rwa [c.next_eq' h]
  have hin : ∀ j ∈ s, v (Abelian.image (K.d (c.prev j) j)) =
      ∑ i ∈ s, if c.Rel i j then v (Abelian.image (K.d i j)) else 0 := by
    intro j _
    by_cases hrel : c.Rel (c.prev j) j
    · by_cases hmem : c.prev j ∈ s
      · rw [Finset.sum_eq_single (c.prev j)]
        · simp [hrel]
        · intro i _ hne
          exact ite_eq_right (fun h ↦ hne (c.prev_eq' h).symm)
        · intro h; exact absurd hmem h
      · rw [P.map_eq_zero_of_isZero hv (isZero_abelianImage_of_isZero_src _ (hs _ hmem))]
        symm
        refine Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hmem ?_
        rwa [c.prev_eq' h]
    · rw [P.map_eq_zero_of_isZero hv (isZero_abelianImage_of_eq_zero (K.shape _ _ hrel))]
      symm
      refine Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hrel ?_
      rwa [c.prev_eq' h]
  -- Expand `v (K.X i)` in the sum and cancel the paired boundary sums using `c.χ_next`.
  have hsum : ∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i) +
      (∑ i ∈ s, ∑ j ∈ s,
        if c.Rel i j then (c.χ i : ℤ) • v (Abelian.image (K.d i j)) else 0) +
      (∑ j ∈ s, ∑ i ∈ s,
        if c.Rel i j then (c.χ j : ℤ) • v (Abelian.image (K.d i j)) else 0) := by
    calc ∑ i ∈ s, (c.χ i : ℤ) • v (K.X i)
        = ∑ i ∈ s, ((c.χ i : ℤ) • v (K.homology i) +
            (c.χ i : ℤ) • v (Abelian.image (K.d i (c.next i))) +
            (c.χ i : ℤ) • v (Abelian.image (K.d (c.prev i) i))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hX i, smul_add, smul_add]
          abel
      _ = ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i) +
          ∑ i ∈ s, (c.χ i : ℤ) • v (Abelian.image (K.d i (c.next i))) +
          ∑ i ∈ s, (c.χ i : ℤ) • v (Abelian.image (K.d (c.prev i) i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          · congr 1
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [hout i hi, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            split_ifs <;> simp
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            rw [hin j hj, Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            split_ifs <;> simp
  have hcancel :
      (∑ i ∈ s, ∑ j ∈ s,
          if c.Rel i j then (c.χ i : ℤ) • v (Abelian.image (K.d i j)) else 0) +
      (∑ j ∈ s, ∑ i ∈ s,
          if c.Rel i j then (c.χ j : ℤ) • v (Abelian.image (K.d i j)) else 0) = 0 := by
    rw [Finset.sum_comm (s := s) (t := s) (f := fun j i ↦
      if c.Rel i j then (c.χ j : ℤ) • v (Abelian.image (K.d i j)) else 0),
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hrel : c.Rel i j
    · simp only [hrel, ↓reduceIte, c.χ_next hrel, Units.val_neg, neg_smul, add_neg_cancel]
    · simp [hrel]
  rw [hsum, add_assoc, hcancel, add_zero]

/-- **Euler--Poincaré for an additive invariant on a finitely supported complex of arbitrary
shape.** This is the specialization of `HomologicalComplex.sum_χ_smul_X_eq_sum_χ_smul_homology`
to `P = ⊤`. -/
theorem sum_χ_smul_obj_X_eq_sum_χ_smul_obj_homology [c.EulerCharSigns]
    (K : HomologicalComplex C c) {G : Type*} [AddCommGroup G]
    (v : TauCeti.AbelianK0.AdditiveInvariant C G)
    (s : Finset ι) (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) • v.obj (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) • v.obj (K.homology i) :=
  K.sum_χ_smul_X_eq_sum_χ_smul_homology ⊤ v.obj (fun _ hS _ _ _ ↦ v.map_shortExact hS) s hs
    (fun _ _ ↦ trivial)

end Abelian

section ModuleCat

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}

/-- The finrank support of a complex of modules vanishing outside `s` is contained in `s`. -/
lemma finrankSupport_X_subset_of_isZero [Nontrivial R]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    (s : Finset ι) (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) :
    GradedObject.finrankSupport K.X ⊆ s := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro i hi
  exact ModuleCat.finrank_eq_zero_of_isZero (hs i (fun h ↦ hi (Finset.mem_coe.2 h)))

/-- The finrank support of the homology of a complex of modules vanishing outside `s` is contained
in `s`. -/
lemma finrankSupport_homology_subset_of_isZero [Nontrivial R]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    (s : Finset ι) (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) :
    GradedObject.finrankSupport (fun i ↦ K.homology i) ⊆ s := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro i hi
  exact ModuleCat.finrank_eq_zero_of_isZero
    ((K.sc i).isZero_homology_of_isZero_X₂ (hs i (fun h ↦ hi (Finset.mem_coe.2 h))))

/-- **Euler--Poincaré for a finitely supported complex of finitely generated modules of arbitrary
shape**, in Mathlib's `HomologicalComplex.eulerChar` API. Over a Noetherian ring with the
rank-nullity property (such as a division ring or `ℤ`), the term and homology Euler
characteristics agree for any complex in `FGModuleCat R` vanishing outside a finite set. -/
theorem eulerChar_forgetFG_eq_homologyEulerChar_of_finset [IsNoetherianRing R]
    [HasRankNullity.{v} R] [c.EulerCharSigns]
    (K : HomologicalComplex (FGModuleCat.{v} R) c) (s : Finset ι)
    (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) :
    eulerChar (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex c).obj K) =
      homologyEulerChar
        (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex c).obj K) := by
  have hsF : ∀ i : ι, i ∉ s →
      IsZero ((((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex c).obj
        K).X i) := fun i hi ↦
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map_isZero (hs i hi)
  rw [eulerChar_eq_sum_finSet_of_finrankSupport_subset _ s
        (finrankSupport_X_subset_of_isZero _ s hsF),
      homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset _ s
        (finrankSupport_homology_subset_of_isZero _ s hsF)]
  have h := K.sum_χ_smul_obj_X_eq_sum_χ_smul_obj_homology
    (TauCeti.AbelianK0.AdditiveInvariant.finrank R) s hs
  simpa only [Functor.mapHomologicalComplex_obj_X, FGModuleCat.finrank_forget₂_obj,
    finrank_homology_forget, TauCeti.AbelianK0.AdditiveInvariant.finrank_obj, smul_eq_mul] using h

/-- **Euler--Poincaré for a finitely supported complex in `ModuleCat R` of arbitrary shape.**
Over a Noetherian ring with the rank-nullity property (such as a division ring or `ℤ`), a complex
of `R`-modules vanishing outside a finite set `s` whose terms in `s` are finitely generated has the
same `eulerChar` and `homologyEulerChar`. -/
theorem eulerChar_eq_homologyEulerChar_of_finset [IsNoetherianRing R] [HasRankNullity.{v} R]
    [c.EulerCharSigns] (K : HomologicalComplex (ModuleCat.{v} R) c) (s : Finset ι)
    (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) (hK : ∀ i ∈ s, Module.Finite R (K.X i)) :
    K.eulerChar = K.homologyEulerChar := by
  classical
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  have hall : ∀ i : ι, Module.Finite R (K.X i) := fun i ↦
    if hi : i ∈ s then hK i hi else
      have := ModuleCat.subsingleton_of_isZero (hs i hi)
      inferInstance
  let L : HomologicalComplex (FGModuleCat.{v} R) c :=
    K.liftObjectProperty (ModuleCat.isFG R) fun i ↦ (ModuleCat.isFG_iff _).2 (hall i)
  let e : (F.mapHomologicalComplex c).obj L ≅ K := K.liftFGModuleCatIso hall
  have hsL : ∀ i : ι, i ∉ s → IsZero (L.X i) := fun i hi ↦
    IsZero.of_full_of_faithful_of_isZero F (L.X i) (hs i hi)
  rw [← eulerChar_eq_of_iso e, ← homologyEulerChar_eq_of_iso e]
  exact L.eulerChar_forgetFG_eq_homologyEulerChar_of_finset s hsL

end ModuleCat

end HomologicalComplex
