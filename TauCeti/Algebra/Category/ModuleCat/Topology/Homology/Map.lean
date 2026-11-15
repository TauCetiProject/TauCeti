/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology.Basic

/-!
# Continuous linear maps on cycles and homology in independent universes

Morphisms in `TopModuleCat R` bind source and target to one universe, so the categorical maps
`HomologicalComplex.cyclesMap` and `HomologicalComplex.homologyMap` apply only to complexes of
topological `R`-modules living in the same universe. Continuous `R`-linear maps `M →L[R] N` and
continuous `R`-linear equivalences `M ≃L[R] N`, by contrast, allow `M` and `N` in independent
universes while still keeping track of the subspace topology on cycles and the quotient topology on
homology.

This file provides the corresponding universal properties and functoriality for `TopModuleCat R`
across independent universes:

* `CategoryTheory.ShortComplex.liftCyclesCLM` lifts a continuous linear map killed by `S.g` to
  `S.cycles`, using the subspace-topology kernel `TopModuleCat.isLimitKer`;
* `CategoryTheory.ShortComplex.descHomologyCLM` upgrades `CategoryTheory.ShortComplex.descHomologyₗ`
  to a continuous linear map out of `S.homology`, using the quotient-topology cokernel
  `CategoryTheory.ShortComplex.homologyIsoCoker`;
* `HomologicalComplex.cyclesMapCLM` and `HomologicalComplex.homologyMapCLM` induce continuous
  linear maps on cycles and homology from any degreewise family of continuous linear maps commuting
  with the differentials between complexes in `TopModuleCat.{v₁} R` and `TopModuleCat.{v₂} R`;
* `HomologicalComplex.cyclesMapCLE` and `HomologicalComplex.homologyMapCLE` upgrade a degreewise
  family of continuous linear equivalences commuting with the differentials to continuous linear
  equivalences on cycles and homology.

In a single universe these agree with the underlying continuous linear maps of
`HomologicalComplex.cyclesMap` and `HomologicalComplex.homologyMap`
(`HomologicalComplex.hom_cyclesMap` and `HomologicalComplex.hom_homologyMap`).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] (S : ShortComplex (TopModuleCat R))

section LiftCycles

variable {W : Type*} [AddCommGroup W] [Module R W] [TopologicalSpace W]

/-- **Lift of a continuous linear map to cycles.** A continuous `R`-linear map into the middle term
of a short complex of topological modules whose image is killed by `S.g` lifts to a continuous
`R`-linear map into `S.cycles`, because `S.cycles` carries the subspace topology of `ker S.g`.
Unlike `CategoryTheory.ShortComplex.liftCycles`, the source `W` is an arbitrary topological module
in any universe rather than an object of the same category `TopModuleCat R`. -/
noncomputable def liftCyclesCLM (f : W →L[R] S.X₂) (hf : ∀ w, S.g (f w) = 0) :
    W →L[R] S.cycles :=
  (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).hom.hom.comp
    (f.codRestrict S.g.hom.ker fun w ↦ hf w)

/-- Composing `liftCyclesCLM` with the cycle inclusion recovers the original map. -/
@[simp]
theorem iCycles_liftCyclesCLM_apply (f : W →L[R] S.X₂) (hf : ∀ w, S.g (f w) = 0) (w : W) :
    S.iCycles (S.liftCyclesCLM f hf w) = f w := by
  have h := ConcreteCategory.congr_hom
    (S.isoCyclesOfIsLimit_hom_iCycles (TopModuleCat.isLimitKer S.g)) ⟨f w, hf w⟩
  simp only [ConcreteCategory.comp_apply, Limits.KernelFork.ι_ofι] at h
  exact h

/-- Pointwise, `liftCyclesCLM` constructs the elementwise cycle `cyclesMkOfEq`. -/
theorem liftCyclesCLM_apply (f : W →L[R] S.X₂) (hf : ∀ w, S.g (f w) = 0) (w : W) :
    S.liftCyclesCLM f hf w = S.cyclesMkOfEq (f w) (hf w) :=
  S.iCycles_injective
    ((S.iCycles_liftCyclesCLM_apply f hf w).trans (S.iCycles_cyclesMkOfEq (f w) (hf w)).symm)

/-- Two continuous linear maps into `S.cycles` are equal as soon as they agree after `S.iCycles`. -/
theorem continuousLinearMap_cycles_ext {f g : W →L[R] S.cycles}
    (h : ∀ w, S.iCycles (f w) = S.iCycles (g w)) : f = g :=
  ContinuousLinearMap.ext fun w ↦ S.iCycles_injective (h w)

end LiftCycles

section DescHomology

variable {W : Type*} [AddCommGroup W] [Module R W] [TopologicalSpace W]

/-- **Descent of a continuous linear map to homology.** A continuous `R`-linear map out of the
cycles of a short complex of topological modules that vanishes on the kernel of `S.homologyπ`
descends to a continuous `R`-linear map out of `S.homology`, because `S.homology` carries the
quotient topology of `TopModuleCat.coker S.toCycles`. Unlike
`CategoryTheory.ShortComplex.descHomology`, the target `W` may live in any universe. -/
noncomputable def descHomologyCLM (k : S.cycles →L[R] W) (hk : ∀ z, S.homologyπ z = 0 → k z = 0) :
    S.homology →L[R] W :=
  ({ toLinearMap := S.toCycles.hom.range.liftQ k.toLinearMap fun z hz ↦
       LinearMap.mem_ker.2 (hk z (S.homologyπ_eq_zero_iff.2 (LinearMap.mem_range.1 hz)))
     cont := Continuous.quotient_lift k.cont _ } :
    TopModuleCat.coker S.toCycles →L[R] W).comp (homologyIsoCoker S).hom.hom

/-- The defining equation of `descHomologyCLM`: on the class of a cycle it takes the given value. -/
@[simp]
theorem descHomologyCLM_π (k : S.cycles →L[R] W) (hk : ∀ z, S.homologyπ z = 0 → k z = 0)
    (z : S.cycles) : S.descHomologyCLM k hk (S.homologyπ z) = k z := by
  have h := ConcreteCategory.congr_hom (homologyπ_comp_homologyIsoCoker_hom S) z
  simp only [ConcreteCategory.comp_apply] at h
  -- Unfold `descHomologyCLM` to the composite across `TopModuleCat.coker S.toCycles`.
  rw [descHomologyCLM, ContinuousLinearMap.comp_apply]
  -- `TopModuleCat.Hom.hom` and `ConcreteCategory.hom` have the same underlying function.
  have h' : (homologyIsoCoker S).hom.hom (S.homologyπ z) = TopModuleCat.cokerπ S.toCycles z := h
  rw [h', TopModuleCat.hom_cokerπ, Submodule.mkQ_apply]
  exact Submodule.liftQ_apply _ k.toLinearMap z

/-- Forgetting continuity turns `descHomologyCLM` into `descHomologyₗ`. -/
@[simp]
theorem toLinearMap_descHomologyCLM (k : S.cycles →L[R] W)
    (hk : ∀ z, S.homologyπ z = 0 → k z = 0) :
    (S.descHomologyCLM k hk).toLinearMap = S.descHomologyₗ k.toLinearMap hk := by
  ext x
  obtain ⟨z, rfl⟩ := S.homologyπ_surjective x
  simp

/-- Two continuous linear maps out of `S.homology` are equal when they agree on every cycle
class. -/
theorem continuousLinearMap_homology_ext {f g : S.homology →L[R] W}
    (h : ∀ z : S.cycles, f (S.homologyπ z) = g (S.homologyπ z)) : f = g := by
  ext x
  obtain ⟨z, rfl⟩ := S.homologyπ_surjective x
  exact h z

end DescHomology

end CategoryTheory.ShortComplex

namespace HomologicalComplex

universe v₁ v₂ v₃

variable {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*} {c : ComplexShape ι}

section DescHomology

variable (K : HomologicalComplex (TopModuleCat.{v₁} R) c) (n : ι)
  {W : Type*} [AddCommGroup W] [Module R W] [TopologicalSpace W]

/-- **Descent of a continuous linear map to degreewise homology.** A continuous `R`-linear map out
of `K.cycles n` that vanishes on the kernel of `K.homologyπ n` descends to `K.homology n`. -/
noncomputable def descHomologyCLM (k : K.cycles n →L[R] W)
    (hk : ∀ z, K.homologyπ n z = 0 → k z = 0) : K.homology n →L[R] W :=
  (K.sc n).descHomologyCLM k hk

/-- On the class of a degree-`n` cycle, `descHomologyCLM` takes the given value. -/
@[simp]
theorem descHomologyCLM_π (k : K.cycles n →L[R] W) (hk : ∀ z, K.homologyπ n z = 0 → k z = 0)
    (z : K.cycles n) : K.descHomologyCLM n k hk (K.homologyπ n z) = k z :=
  (K.sc n).descHomologyCLM_π k hk z

/-- Two continuous linear maps out of `K.homology n` are equal when they agree on all cycle
classes. -/
theorem continuousLinearMap_homology_ext {f g : K.homology n →L[R] W}
    (h : ∀ z : K.cycles n, f (K.homologyπ n z) = g (K.homologyπ n z)) : f = g :=
  (K.sc n).continuousLinearMap_homology_ext h

end DescHomology

section MapCLM

variable (K : HomologicalComplex (TopModuleCat.{v₁} R) c)
  (L : HomologicalComplex (TopModuleCat.{v₂} R) c)

/-- A family of degreewise continuous linear maps commuting with differentials along `c.Rel`
commutes with `d i j` for all pairs of degrees `(i, j)`, non-adjacent differentials being zero. -/
theorem comm_d_of_rel (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (i j : ι) (x : K.X i) :
    (L.d i j).hom (f i x) = f j ((K.d i j).hom x) := by
  by_cases hij : c.Rel i j
  · exact hf i j hij x
  · rw [K.shape i j hij, L.shape i j hij, TopModuleCat.hom_zero, TopModuleCat.hom_zero,
      zero_apply, zero_apply, map_zero]

/-- **Induced continuous linear map on cycles across universes.** Given complexes `K` and `L` of
topological `R`-modules in independent universes and continuous linear maps
`f i : K.X i →L[R] L.X i` commuting with the differentials, `cyclesMapCLM` is the induced
continuous linear map on degree-`n` cycles. -/
noncomputable def cyclesMapCLM (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x)) (n : ι) :
    K.cycles n →L[R] L.cycles n :=
  (L.sc n).liftCyclesCLM ((f n).comp (K.iCycles n).hom) fun z ↦ by
    rw [shortComplexFunctor_obj_g, ContinuousLinearMap.comp_apply,
      comm_d_of_rel K L f hf n (c.next n), K.d_iCycles_apply, map_zero]

/-- The cycle inclusion intertwines `cyclesMapCLM` with `f n`. -/
@[simp]
theorem iCycles_cyclesMapCLM_apply (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (n : ι) (z : K.cycles n) :
    L.iCycles n (cyclesMapCLM K L f hf n z) = f n (K.iCycles n z) :=
  (L.sc n).iCycles_liftCyclesCLM_apply _ _ z

/-- On an elementwise cycle `cyclesMkOfEq`, `cyclesMapCLM` applies `f n` to the underlying
element. -/
@[simp]
theorem cyclesMapCLM_cyclesMkOfEq (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    {n : ι} (x : K.X n) (j : ι) (hj : c.next n = j) (hx : (K.d n j).hom x = 0) :
    cyclesMapCLM K L f hf n (K.cyclesMkOfEq x j hj hx) =
      L.cyclesMkOfEq (f n x) j hj (by rw [comm_d_of_rel K L f hf n j, hx, map_zero]) := by
  apply L.iCycles_injective n
  rw [iCycles_cyclesMapCLM_apply, iCycles_cyclesMkOfEq, iCycles_cyclesMkOfEq]

/-- `cyclesMapCLM` carries boundaries `toCycles m n x` to boundaries `toCycles m n (f m x)`. -/
@[simp]
theorem cyclesMapCLM_toCycles_apply (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (m n : ι) (x : K.X m) :
    cyclesMapCLM K L f hf n (K.toCycles m n x) = L.toCycles m n (f m x) := by
  apply L.iCycles_injective n
  rw [iCycles_cyclesMapCLM_apply, iCycles_toCycles_apply, iCycles_toCycles_apply,
    comm_d_of_rel K L f hf m n]

/-- Two degreewise maps agreeing on cycles in degree `n` induce the same map on `cycles n`. -/
theorem cyclesMapCLM_congr {f g : ∀ i, K.X i →L[R] L.X i}
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (hg : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (g i x) = g j ((K.d i j).hom x))
    {n : ι} (hfg : ∀ z : K.cycles n, f n (K.iCycles n z) = g n (K.iCycles n z)) :
    cyclesMapCLM K L f hf n = cyclesMapCLM K L g hg n := by
  ext z
  apply L.iCycles_injective n
  rw [iCycles_cyclesMapCLM_apply, iCycles_cyclesMapCLM_apply, hfg z]

/-- **Induced continuous linear map on homology across universes.** Given complexes `K` and `L` of
topological `R`-modules in independent universes and continuous linear maps
`f i : K.X i →L[R] L.X i` commuting with the differentials, `homologyMapCLM` is the induced
continuous linear map on degree-`n` homology, carrying the class of a cycle to the class of its
image under `cyclesMapCLM`. -/
noncomputable def homologyMapCLM (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x)) (n : ι) :
    K.homology n →L[R] L.homology n :=
  K.descHomologyCLM n ((L.homologyπ n).hom.comp (cyclesMapCLM K L f hf n)) fun z hz ↦ by
    obtain ⟨x, rfl⟩ := (K.homologyπ_eq_zero_iff n rfl).1 hz
    rw [ContinuousLinearMap.comp_apply, cyclesMapCLM_toCycles_apply]
    exact (L.homologyπ_eq_zero_iff n rfl).2 ⟨f (c.prev n) x, rfl⟩

/-- `homologyMapCLM` carries the homology class of a cycle to the class of its mapped cycle. -/
@[simp]
theorem homologyMapCLM_homologyπ (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (n : ι) (z : K.cycles n) :
    homologyMapCLM K L f hf n (K.homologyπ n z) =
      L.homologyπ n (cyclesMapCLM K L f hf n z) :=
  K.descHomologyCLM_π n _ _ z

/-- On the class of an elementwise cycle `cyclesMkOfEq`, `homologyMapCLM` applies `f n` to the
representative. -/
theorem homologyMapCLM_homologyπ_cyclesMkOfEq (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    {n : ι} (x : K.X n) (j : ι) (hj : c.next n = j) (hx : (K.d n j).hom x = 0) :
    homologyMapCLM K L f hf n (K.homologyπ n (K.cyclesMkOfEq x j hj hx)) =
      L.homologyπ n (L.cyclesMkOfEq (f n x) j hj
        (by rw [comm_d_of_rel K L f hf n j, hx, map_zero])) := by
  rw [homologyMapCLM_homologyπ, cyclesMapCLM_cyclesMkOfEq]

/-- Two degreewise maps agreeing on cycles in degree `n` induce the same map on `homology n`. -/
theorem homologyMapCLM_congr {f g : ∀ i, K.X i →L[R] L.X i}
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (hg : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (g i x) = g j ((K.d i j).hom x))
    {n : ι} (hfg : ∀ z : K.cycles n, f n (K.iCycles n z) = g n (K.iCycles n z)) :
    homologyMapCLM K L f hf n = homologyMapCLM K L g hg n := by
  refine K.continuousLinearMap_homology_ext n fun z ↦ ?_
  rw [homologyMapCLM_homologyπ, homologyMapCLM_homologyπ, cyclesMapCLM_congr K L hf hg hfg]

end MapCLM

section Functoriality

variable (K : HomologicalComplex (TopModuleCat.{v₁} R) c)
  (L : HomologicalComplex (TopModuleCat.{v₂} R) c)
  (M : HomologicalComplex (TopModuleCat.{v₃} R) c)

/-- The identity family of continuous linear maps induces the identity on cycles. -/
@[simp]
theorem cyclesMapCLM_id (n : ι)
    (hid : ∀ i j, c.Rel i j → ∀ x,
      (K.d i j).hom (ContinuousLinearMap.id R (K.X i) x) =
        ContinuousLinearMap.id R (K.X j) ((K.d i j).hom x) := fun _ _ _ _ ↦ rfl) :
    cyclesMapCLM K K (fun i ↦ ContinuousLinearMap.id R (K.X i)) hid n =
      ContinuousLinearMap.id R (K.cycles n) := by
  ext z
  apply K.iCycles_injective n
  simp

/-- `cyclesMapCLM` respects composition across three independent universes. -/
theorem cyclesMapCLM_comp (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (g : ∀ i, L.X i →L[R] M.X i)
    (hg : ∀ i j, c.Rel i j → ∀ y, (M.d i j).hom (g i y) = g j ((L.d i j).hom y))
    (n : ι) :
    cyclesMapCLM K M (fun i ↦ (g i).comp (f i))
        (fun i j hij x ↦ by simp [hf i j hij, hg i j hij]) n =
      (cyclesMapCLM L M g hg n).comp (cyclesMapCLM K L f hf n) := by
  ext z
  apply M.iCycles_injective n
  simp

/-- The identity family of continuous linear maps induces the identity on homology. -/
@[simp]
theorem homologyMapCLM_id (n : ι)
    (hid : ∀ i j, c.Rel i j → ∀ x,
      (K.d i j).hom (ContinuousLinearMap.id R (K.X i) x) =
        ContinuousLinearMap.id R (K.X j) ((K.d i j).hom x) := fun _ _ _ _ ↦ rfl) :
    homologyMapCLM K K (fun i ↦ ContinuousLinearMap.id R (K.X i)) hid n =
      ContinuousLinearMap.id R (K.homology n) := by
  refine K.continuousLinearMap_homology_ext n fun z ↦ ?_
  simp

/-- `homologyMapCLM` respects composition across three independent universes. -/
theorem homologyMapCLM_comp (f : ∀ i, K.X i →L[R] L.X i)
    (hf : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (f i x) = f j ((K.d i j).hom x))
    (g : ∀ i, L.X i →L[R] M.X i)
    (hg : ∀ i j, c.Rel i j → ∀ y, (M.d i j).hom (g i y) = g j ((L.d i j).hom y))
    (n : ι) :
    homologyMapCLM K M (fun i ↦ (g i).comp (f i))
        (fun i j hij x ↦ by simp [hf i j hij, hg i j hij]) n =
      (homologyMapCLM L M g hg n).comp (homologyMapCLM K L f hf n) := by
  refine K.continuousLinearMap_homology_ext n fun z ↦ ?_
  rw [ContinuousLinearMap.comp_apply, homologyMapCLM_homologyπ, homologyMapCLM_homologyπ,
    homologyMapCLM_homologyπ, cyclesMapCLM_comp K L M f hf g hg n, ContinuousLinearMap.comp_apply]

end Functoriality

section SameUniverse

variable {K L : HomologicalComplex (TopModuleCat.{v₁} R) c}

/-- In a single universe, `cyclesMapCLM` is the underlying continuous linear map of the categorical
`HomologicalComplex.cyclesMap`. -/
theorem hom_cyclesMap (φ : K ⟶ L) (n : ι) :
    (cyclesMap φ n).hom =
      cyclesMapCLM K L (fun i ↦ (φ.f i).hom) (fun i j _ x ↦ φ.comm_apply i j x) n := by
  ext z
  apply L.iCycles_injective n
  have h := ConcreteCategory.congr_hom (cyclesMap_i φ n) z
  simpa only [ConcreteCategory.comp_apply, iCycles_cyclesMapCLM_apply] using h

/-- In a single universe, `homologyMapCLM` is the underlying continuous linear map of the
categorical `HomologicalComplex.homologyMap`. -/
theorem hom_homologyMap (φ : K ⟶ L) (n : ι) :
    (homologyMap φ n).hom =
      homologyMapCLM K L (fun i ↦ (φ.f i).hom) (fun i j _ x ↦ φ.comm_apply i j x) n := by
  refine K.continuousLinearMap_homology_ext n fun z ↦ ?_
  have h := ConcreteCategory.congr_hom (homologyπ_naturality φ n) z
  simp only [ConcreteCategory.comp_apply] at h
  rw [homologyMapCLM_homologyπ, ← hom_cyclesMap]
  exact h

end SameUniverse

section MapCLE

variable (K : HomologicalComplex (TopModuleCat.{v₁} R) c)
  (L : HomologicalComplex (TopModuleCat.{v₂} R) c)

/-- If degreewise continuous linear equivalences commute with the differentials, so do their
inverses. -/
theorem symm_comm_d (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x))
    (i j : ι) (hij : c.Rel i j) (y : L.X i) :
    (K.d i j).hom ((e i).symm y) = (e j).symm ((L.d i j).hom y) :=
  (e j).injective (by simp [← he i j hij])

/-- **Induced continuous linear equivalence on cycles across universes.** -/
noncomputable def cyclesMapCLE (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x)) (n : ι) :
    K.cycles n ≃L[R] L.cycles n :=
  ContinuousLinearEquiv.equivOfInverse
    (cyclesMapCLM K L (fun i ↦ (e i).toContinuousLinearMap) he n)
    (cyclesMapCLM L K (fun i ↦ (e i).symm.toContinuousLinearMap) (symm_comm_d K L e he) n)
    (fun z ↦ by
      have h := DFunLike.congr_fun
        (cyclesMapCLM_comp K L K (fun i ↦ (e i).toContinuousLinearMap) he
          (fun i ↦ (e i).symm.toContinuousLinearMap) (symm_comm_d K L e he) n) z
      simpa using h.symm)
    (fun z ↦ by
      have h := DFunLike.congr_fun
        (cyclesMapCLM_comp L K L (fun i ↦ (e i).symm.toContinuousLinearMap)
          (symm_comm_d K L e he) (fun i ↦ (e i).toContinuousLinearMap) he n) z
      simpa using h.symm)

/-- The forward map of `cyclesMapCLE` is `cyclesMapCLM` along `e`. -/
@[simp]
theorem cyclesMapCLE_apply (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x))
    (n : ι) (z : K.cycles n) :
    cyclesMapCLE K L e he n z =
      cyclesMapCLM K L (fun i ↦ (e i).toContinuousLinearMap) he n z :=
  (rfl)

/-- The inverse of `cyclesMapCLE` is `cyclesMapCLM` along `e.symm`. -/
@[simp]
theorem cyclesMapCLE_symm_apply (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x))
    (n : ι) (z : L.cycles n) :
    (cyclesMapCLE K L e he n).symm z =
      cyclesMapCLM L K (fun i ↦ (e i).symm.toContinuousLinearMap) (symm_comm_d K L e he) n z :=
  (rfl)

/-- **Induced continuous linear equivalence on homology across universes.** -/
noncomputable def homologyMapCLE (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x)) (n : ι) :
    K.homology n ≃L[R] L.homology n :=
  ContinuousLinearEquiv.equivOfInverse
    (homologyMapCLM K L (fun i ↦ (e i).toContinuousLinearMap) he n)
    (homologyMapCLM L K (fun i ↦ (e i).symm.toContinuousLinearMap) (symm_comm_d K L e he) n)
    (fun x ↦ by
      have h := DFunLike.congr_fun
        (homologyMapCLM_comp K L K (fun i ↦ (e i).toContinuousLinearMap) he
          (fun i ↦ (e i).symm.toContinuousLinearMap) (symm_comm_d K L e he) n) x
      simpa using h.symm)
    (fun x ↦ by
      have h := DFunLike.congr_fun
        (homologyMapCLM_comp L K L (fun i ↦ (e i).symm.toContinuousLinearMap)
          (symm_comm_d K L e he) (fun i ↦ (e i).toContinuousLinearMap) he n) x
      simpa using h.symm)

/-- The forward map of `homologyMapCLE` is `homologyMapCLM` along `e`. -/
@[simp]
theorem homologyMapCLE_apply (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x))
    (n : ι) (x : K.homology n) :
    homologyMapCLE K L e he n x =
      homologyMapCLM K L (fun i ↦ (e i).toContinuousLinearMap) he n x :=
  (rfl)

/-- The inverse of `homologyMapCLE` is `homologyMapCLM` along `e.symm`. -/
@[simp]
theorem homologyMapCLE_symm_apply (e : ∀ i, K.X i ≃L[R] L.X i)
    (he : ∀ i j, c.Rel i j → ∀ x, (L.d i j).hom (e i x) = e j ((K.d i j).hom x))
    (n : ι) (x : L.homology n) :
    (homologyMapCLE K L e he n).symm x =
      homologyMapCLM L K (fun i ↦ (e i).symm.toContinuousLinearMap) (symm_comm_d K L e he) n x :=
  (rfl)

end MapCLE

end HomologicalComplex
