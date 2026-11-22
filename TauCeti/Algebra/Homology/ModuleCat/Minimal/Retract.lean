/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.ModuleCat.Minimal.Basic
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Data.Int.Interval
import TauCeti.LinearAlgebra.LinearMap.Ker
import TauCeti.RingTheory.LocalRing.Module

/-!
# Minimal deformation retracts of finite projective complexes

Let `(R, 𝔪)` be a local ring and `C` a complex of finite projective `R`-modules with only finitely
many nonzero terms. Then `C` has a *minimal* deformation retract: a minimal complex `N` of finite
free modules (every differential lands in `𝔪` times its target) together with chain maps
`N ⟶ C` and `C ⟶ N` whose composite `N ⟶ C ⟶ N` is `𝟙 N` on the nose and whose composite
`C ⟶ N ⟶ C` is homotopic to `𝟙 C`. The terms of `N` are direct summands of those of `C`, so
`N` vanishes wherever `C` does; in particular a bounded cochain complex retracts onto a minimal
one in the same term interval.

The proof cancels contractible disks one at a time. If a differential `d : Cⁱ ⟶ Cʲ` sends some
`y` outside `𝔪 Cʲ`, a linear form `s : Cʲ → R` takes the value `1` at `d y`. The homotopy
`z ↦ s z • y` from `Cʲ` to `Cⁱ` produces the null-homotopic chain map `π` with
`π y' = s (d y') • y` in degree `i`, `π z = s z • d y` in degree `j`, and `0` elsewhere. It is an
idempotent projecting onto the disk `R y ⟶ R (d y)`, so its kernel is a deformation retract of
`C` (`HomotopyEquiv.ofKernel`) whose ranks drop by one in degrees `i` and `j` and are unchanged
elsewhere. Induction on the total rank ends at a minimal complex. By
`HomologicalComplex.IsMinimal.isIso_hom_of_homotopyEquiv` the minimal retract is unique up to
isomorphism of complexes.

The shape is assumed to have no loops `c.Rel i i`, as for chain and cochain complexes indexed by
`ℕ` or `ℤ`, so that the two degrees of a disk are distinct.

## Main results

* `HomologicalComplex.exists_homotopyEquiv_of_d_apply_notMem`: a differential with a value outside
  `𝔪` times its target splits off a disk, lowering the ranks in its two degrees by one.
* `HomologicalComplex.exists_isMinimal_homotopyEquiv`: a complex of finite projective modules over
  a local ring with finitely many nonzero terms has a minimal deformation retract with finite free
  terms.
* `CochainComplex.exists_isMinimal_homotopyEquiv`: the same for a bounded cochain complex, with
  the minimal retract supported in the same interval.

## References

* C. Khare, J. A. Thorne, *Potential automorphy and the Leopoldt conjecture*, Amer. J. Math. 139
  (2017), 1205–1273, Section 2.2, Lemma 2.3: minimal complexes.
* The Stacks Project, Lemma 15.77.6 (0BCC), for cancelling unit entries of finite free complexes.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

section Cancellation

variable (C : HomologicalComplex (ModuleCat.{v} R) c) {i j : ι} (y : C.X i) (s : C.X j →ₗ[R] R)

open scoped Classical in
/-- The components of the homotopy `z ↦ s z • y` from degree `j` to degree `i`, zero elsewhere. -/
private noncomputable def cancelHom (k l : ι) : C.X k ⟶ C.X l :=
  if h : k = j ∧ l = i then
    eqToHom (congrArg C.X h.1) ≫ ModuleCat.ofHom (s.smulRight y) ≫ eqToHom (congrArg C.X h.2.symm)
  else 0

private theorem cancelHom_self : cancelHom C y s j i = ModuleCat.ofHom (s.smulRight y) := by
  simp [cancelHom]

private theorem cancelHom_of_ne_left {k l : ι} (hk : k ≠ j) : cancelHom C y s k l = 0 := by
  simp [cancelHom, hk]

private theorem cancelHom_of_ne_right {k l : ι} (hl : l ≠ i) : cancelHom C y s k l = 0 := by
  simp [cancelHom, hl]

/-- The null-homotopic chain map `d h + h d` of the homotopy `h = cancelHom`. -/
private noncomputable def cancelMap : C ⟶ C :=
  Homotopy.nullHomotopicMap (cancelHom C y s)

private theorem cancelMap_f (k : ι) :
    (cancelMap C y s).f k = dNext k (cancelHom C y s) + prevD k (cancelHom C y s) :=
  (rfl)

variable {C y s}

private theorem cancelMap_f_left (hij : c.Rel i j) (hne : i ≠ j) :
    ((cancelMap C y s).f i).hom = (s ∘ₗ (C.d i j).hom).smulRight y := by
  have h : prevD i (cancelHom C y s) = 0 := by
    simp [prevD, cancelHom_of_ne_left C y s hne]
  rw [cancelMap_f, dNext_eq _ hij, h, add_zero, cancelHom_self]
  ext y'
  simp

private theorem cancelMap_f_right (hij : c.Rel i j) (hne : i ≠ j) :
    ((cancelMap C y s).f j).hom = s.smulRight ((C.d i j).hom y) := by
  have h : dNext j (cancelHom C y s) = 0 := by
    simp [dNext, cancelHom_of_ne_right C y s hne.symm]
  rw [cancelMap_f, prevD_eq _ hij, h, zero_add, cancelHom_self]
  ext z
  simp

private theorem cancelMap_f_of_ne {k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    (cancelMap C y s).f k = 0 := by
  simp [cancelMap_f, dNext, prevD, cancelHom_of_ne_right C y s hki,
    cancelHom_of_ne_left C y s hkj]

private theorem cancelMap_idem (hij : c.Rel i j) (hne : i ≠ j) (hs : s ((C.d i j).hom y) = 1) :
    cancelMap C y s ≫ cancelMap C y s = cancelMap C y s := by
  ext k : 2
  by_cases hki : k = i
  · subst hki
    ext y'
    simp [cancelMap_f_left hij hne, hs]
  by_cases hkj : k = j
  · subst hkj
    ext z
    simp [cancelMap_f_right hij hne, hs]
  simp [cancelMap_f_of_ne hki hkj]

/-- The null-homotopy of `cancelMap`. -/
private noncomputable def cancelHomotopy (hij : c.Rel i j) : Homotopy (cancelMap C y s) 0 :=
  Homotopy.nullHomotopy _ fun k l hlk ↦ by
    by_cases hk : k = j
    · subst hk
      exact cancelHom_of_ne_right C y s fun hl ↦ hlk (hl ▸ hij)
    · exact cancelHom_of_ne_left C y s hk

end Cancellation

/-- A differential with a value outside `𝔪` times its target is one allowed by the shape. -/
private theorem rel_of_d_apply_notMem {C : HomologicalComplex (ModuleCat.{v} R) c} {I : Ideal R}
    {i j : ι} {y : C.X i} (hy : (C.d i j).hom y ∉ I • (⊤ : Submodule R (C.X j))) : c.Rel i j := by
  by_contra h
  simp [C.shape i j h] at hy

/-- **Cancelling a disk.** Let `C` be a complex of finite projective modules over a local ring
`(R, 𝔪)`, and suppose the differential `d : Cⁱ ⟶ Cʲ`, with `i ≠ j`, sends some `y` outside
`𝔪 Cʲ` (so that `c.Rel i j`). Then `C` has a deformation retract `N`, with finite free terms,
whose ranks are those of `C` lowered by one in degrees `i` and `j`: chain maps `e.hom : N ⟶ C`
and `e.inv : C ⟶ N` with `e.hom ≫ e.inv = 𝟙 N` and `e.inv ≫ e.hom` homotopic to `𝟙 C`. -/
theorem exists_homotopyEquiv_of_d_apply_notMem [IsLocalRing R]
    (C : HomologicalComplex (ModuleCat.{v} R) c) [∀ k, Module.Projective R (C.X k)]
    [∀ k, Module.Finite R (C.X k)] {i j : ι} (hne : i ≠ j) {y : C.X i}
    (hy : (C.d i j).hom y ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.X j))) :
    ∃ (N : HomologicalComplex (ModuleCat.{v} R) c) (e : HomotopyEquiv N C),
      e.hom ≫ e.inv = 𝟙 N ∧ (∀ k, Module.Free R (N.X k) ∧ Module.Finite R (N.X k)) ∧
      finrank R (N.X i) + 1 = finrank R (C.X i) ∧ finrank R (N.X j) + 1 = finrank R (C.X j) ∧
      ∀ k, k ≠ i → k ≠ j → finrank R (N.X k) = finrank R (C.X k) := by
  have hij := rel_of_d_apply_notMem hy
  obtain ⟨s, hs⟩ := Module.isUnimodular_iff.1
    (TauCeti.IsLocalRing.isUnimodular_iff_notMem_maximalIdeal_smul.2 hy)
  let p := cancelMap C y s
  let e := HomotopyEquiv.ofKernel p (cancelMap_idem hij hne hs) (cancelHomotopy hij)
  -- In each degree the term of `kernel p` is the kernel of a linear form taking the value `1`,
  -- in degrees `i` and `j`, and all of `C` elsewhere.
  have hi := TauCeti.IsLocalRing.finrank_ker_add_one_of_apply_eq_one
    (φ := s ∘ₗ (C.d i j).hom) (w := y) hs
  have hj := TauCeti.IsLocalRing.finrank_ker_add_one_of_apply_eq_one
    (φ := s) (w := (C.d i j).hom y) hs
  have hki : LinearMap.ker (p.f i).hom = LinearMap.ker (s ∘ₗ (C.d i j).hom) := by
    rw [cancelMap_f_left hij hne,
      LinearMap.ker_smulRight_of_apply_eq_one (φ := s ∘ₗ (C.d i j).hom) hs]
  have hkj : LinearMap.ker (p.f j).hom = LinearMap.ker s := by
    rw [cancelMap_f_right hij hne, LinearMap.ker_smulRight_of_apply_eq_one hs]
  have hk {k : ι} (h₁ : k ≠ i) (h₂ : k ≠ j) : LinearMap.ker (p.f k).hom = ⊤ := by
    rw [cancelMap_f_of_ne h₁ h₂, ModuleCat.hom_zero, LinearMap.ker_zero]
  -- The terms of the kernel of a chain map are the kernels of its components.
  let ek (k : ι) : (kernel p).X k ≃ₗ[R] LinearMap.ker (p.f k).hom :=
    (PreservesKernel.iso (eval _ c k) p ≪≫ ModuleCat.kernelIsoKer (p.f k)).toLinearEquiv
  refine ⟨kernel p, e, by simp [e], fun k ↦ ?_, ?_, ?_, ?_⟩
  · suffices Module.Free R (LinearMap.ker (p.f k).hom) ∧
        Module.Finite R (LinearMap.ker (p.f k).hom) by
      obtain ⟨_, _⟩ := this
      exact ⟨.of_equiv (ek k).symm, .equiv (ek k).symm⟩
    by_cases h₁ : k = i
    · subst h₁
      rw [hki]
      exact ⟨hi.1, hi.2.1⟩
    by_cases h₂ : k = j
    · subst h₂
      rw [hkj]
      exact ⟨hj.1, hj.2.1⟩
    rw [hk h₁ h₂]
    have : Module.Finite R (⊤ : Submodule R (C.X k)) := .equiv Submodule.topEquiv.symm
    have : Module.Projective R (⊤ : Submodule R (C.X k)) := .of_equiv Submodule.topEquiv.symm
    exact ⟨Module.free_of_projective_of_isLocalRing, ‹_›⟩
  · rw [(ek i).finrank_eq, hki, hi.2.2]
  · rw [(ek j).finrank_eq, hkj, hj.2.2]
  · intro k h₁ h₂
    rw [(ek k).finrank_eq, hk h₁ h₂, finrank_top]

/-- **Minimal deformation retracts.** A complex `C` of finite projective modules over a local ring,
with finitely many nonzero terms and indexed by a shape without loops, retracts by deformation onto
a minimal complex `N` of finite free modules: there are chain maps `e.hom : N ⟶ C` and
`e.inv : C ⟶ N` with `e.hom ≫ e.inv = 𝟙 N` and `e.inv ≫ e.hom` homotopic to `𝟙 C`. As a
retract, `N` vanishes in every degree where `C` does. -/
theorem exists_isMinimal_homotopyEquiv [IsLocalRing R] (hc : ∀ k, ¬ c.Rel k k)
    (C : HomologicalComplex (ModuleCat.{v} R) c) [∀ k, Module.Projective R (C.X k)]
    [∀ k, Module.Finite R (C.X k)] (hC : {k | ¬ IsZero (C.X k)}.Finite) :
    ∃ (N : HomologicalComplex (ModuleCat.{v} R) c) (e : HomotopyEquiv N C),
      N.IsMinimal ∧ e.hom ≫ e.inv = 𝟙 N ∧ (∀ k, IsZero (C.X k) → IsZero (N.X k)) ∧
        ∀ k, Module.Free R (N.X k) ∧ Module.Finite R (N.X k) := by
  set S := hC.toFinset
  -- Induction on the total rank `∑ k ∈ S, rank Cᵏ`, over complexes vanishing outside `S`.
  suffices H : ∀ (n : ℕ) (C : HomologicalComplex (ModuleCat.{v} R) c)
      [∀ k, Module.Projective R (C.X k)] [∀ k, Module.Finite R (C.X k)],
      (∀ k ∉ S, IsZero (C.X k)) → ∑ k ∈ S, finrank R (C.X k) ≤ n →
      ∃ (N : HomologicalComplex (ModuleCat.{v} R) c) (e : HomotopyEquiv N C),
        N.IsMinimal ∧ e.hom ≫ e.inv = 𝟙 N ∧ (∀ k, IsZero (C.X k) → IsZero (N.X k)) ∧
          ∀ k, Module.Free R (N.X k) ∧ Module.Finite R (N.X k) from
    H _ C (fun k hk ↦ by simpa [S] using hk) le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C _ _ hCS hn
  by_cases hmin : C.IsMinimal
  · exact ⟨C, HomotopyEquiv.refl C, hmin, by simp, fun _ h ↦ h,
      fun k ↦ ⟨Module.free_of_projective_of_isLocalRing, inferInstance⟩⟩
  simp only [isMinimal_iff_range_le_maximalIdeal_smul, not_forall, IsConcreteLE.not_le_iff_exists,
    LinearMap.mem_range] at hmin
  obtain ⟨i, j, _, ⟨y, rfl⟩, hy⟩ := hmin
  have hij := rel_of_d_apply_notMem hy
  have hne : i ≠ j := fun h ↦ hc i (h ▸ hij)
  obtain ⟨N, e, he, hN, hNi, hNj, hNk⟩ := C.exists_homotopyEquiv_of_d_apply_notMem hne hy
  have : ∀ k, Module.Projective R (N.X k) := fun k ↦ have := (hN k).1; inferInstance
  have : ∀ k, Module.Finite R (N.X k) := fun k ↦ (hN k).2
  -- `N` is a retract of `C` in each degree, so it vanishes where `C` does.
  have hNC (k : ι) (hk : IsZero (C.X k)) : IsZero (N.X k) := by
    have : IsSplitMono (e.hom.f k) := IsSplitMono.mk' ⟨e.inv.f k, by rw [← comp_f, he, id_f]⟩
    exact hk.of_mono (e.hom.f k)
  -- The total rank drops, since it drops in degree `i`, where `C` does not vanish.
  have hlt : ∑ k ∈ S, finrank R (N.X k) < ∑ k ∈ S, finrank R (C.X k) := by
    have hiS : i ∈ S := by
      by_contra hiS
      have : Subsingleton (C.X i) := ModuleCat.subsingleton_of_isZero (hCS i hiS)
      exact hy (by simp [Subsingleton.elim y 0])
    refine Finset.sum_lt_sum (fun k _ ↦ ?_) ⟨i, hiS, by lia⟩
    by_cases h₁ : k = i
    · subst h₁; lia
    by_cases h₂ : k = j
    · subst h₂; lia
    exact (hNk k h₁ h₂).le
  obtain ⟨N', e', hN', he', hN'N, hfree⟩ :=
    ih _ (lt_of_lt_of_le hlt hn) N (fun k hk ↦ hNC k (hCS k hk)) le_rfl
  exact ⟨N', e'.trans e, hN', by simp [reassoc_of% he, he'], fun k hk ↦ hN'N k (hNC k hk),
    hfree⟩

end HomologicalComplex

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **Minimal deformation retracts of bounded complexes.** A cochain complex of finite projective
modules over a local ring, concentrated in degrees `a ≤ k ≤ b`, retracts by deformation onto a
minimal complex of finite free modules concentrated in the same degrees. -/
theorem exists_isMinimal_homotopyEquiv (C : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b] [∀ k, Module.Projective R (C.X k)]
    [∀ k, Module.Finite R (C.X k)] :
    ∃ (N : CochainComplex (ModuleCat.{v} R) ℤ) (e : HomotopyEquiv N C),
      N.IsMinimal ∧ e.hom ≫ e.inv = 𝟙 N ∧ N.IsStrictlyGE a ∧ N.IsStrictlyLE b ∧
        ∀ k, Module.Free R (N.X k) ∧ Module.Finite R (N.X k) := by
  have hC : {k | ¬ IsZero (C.X k)}.Finite := (Set.finite_Icc a b).subset fun k hk ↦ by
    by_contra h
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · exact hk (C.isZero_of_isStrictlyGE a k h)
    · exact hk (C.isZero_of_isStrictlyLE b k h)
  obtain ⟨N, e, hN, he, hzero, hfree⟩ :=
    HomologicalComplex.exists_isMinimal_homotopyEquiv (fun k ↦ by simp) C hC
  refine ⟨N, e, hN, he, (isStrictlyGE_iff N a).2 fun k hk ↦ hzero k
    (C.isZero_of_isStrictlyGE a k hk), (isStrictlyLE_iff N b).2 fun k hk ↦ hzero k
    (C.isZero_of_isStrictlyLE b k hk), hfree⟩

end CochainComplex
