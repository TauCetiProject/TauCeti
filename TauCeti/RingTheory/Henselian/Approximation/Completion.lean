/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# Completion for the filtration `tⁿ I`

For a commutative ring `R`, an element `t` and an ideal `I`, the `(t, I)`-adic
completion is the ring of compatible residues in `R / tⁿ I`, with discrete residue
rings. It is a complete Hausdorff topological ring, and the canonical map from `R`
has dense image. Its kernel is the intersection of the ideals `tⁿ I`.

This filtration must not be replaced by powers of `tI`: when `t = 1`, its completion
is `R / I`, not the `I`-adic completion. No regularity, noetherianity or henselianity
hypothesis is needed for these constructions.

The topology uses Mathlib's `RingSubgroupsBasis`, following `Ideal.adic_basis`
by Patrick Massot. The inverse limit uses the existing quotient, product and subring APIs.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §5.4, Definitions 5.4.10–5.4.11.
-/

public section

open Filter Topology

namespace TauCeti.HenselianApproximation

variable {R : Type*} [CommRing R]

/-- The `n`-th ideal in the `(t, I)`-adic filtration. -/
def filtrationIdeal (t : R) (I : Ideal R) (n : ℕ) : Ideal R :=
  ((Ideal.span {t}).stableFiltration I).N n

/-- The filtration uses a power of the parameter ideal, multiplied by `I` only once. -/
theorem filtrationIdeal_def (t : R) (I : Ideal R) (n : ℕ) :
    filtrationIdeal t I n = Ideal.span {t} ^ n * I := by
  simp only [filtrationIdeal, Ideal.stableFiltration_N, Ideal.smul_eq_mul]

/-- The ideals `tⁿ I` decrease with `n`. -/
theorem filtrationIdeal_antitone (t : R) (I : Ideal R) : Antitone (filtrationIdeal t I) :=
  ((Ideal.span {t}).stableFiltration I).antitone

@[simp]
theorem filtrationIdeal_zero (t : R) (I : Ideal R) : filtrationIdeal t I 0 = I := by
  simp [filtrationIdeal_def]

@[simp]
theorem filtrationIdeal_one (I : Ideal R) (n : ℕ) : filtrationIdeal (1 : R) I n = I := by
  simp [filtrationIdeal_def, Ideal.top_pow]

@[simp]
theorem filtrationIdeal_bot (t : R) (n : ℕ) : filtrationIdeal t (⊥ : Ideal R) n = ⊥ := by
  simp [filtrationIdeal_def]

private theorem filtrationBasis (t : R) (I : Ideal R) :
    RingSubgroupsBasis (fun n ↦ (filtrationIdeal t I n).toAddSubgroup) where
  inter m n := ⟨max m n, le_inf
    (filtrationIdeal_antitone t I (le_max_left _ _))
    (filtrationIdeal_antitone t I (le_max_right _ _))⟩
  mul n := ⟨n, by
    rintro _ ⟨a, _, b, hb, rfl⟩
    exact (filtrationIdeal t I n).mul_mem_left a hb⟩
  leftMul a n := ⟨n, fun _ hb ↦ (filtrationIdeal t I n).mul_mem_left a hb⟩
  rightMul a n := ⟨n, fun _ hb ↦ (filtrationIdeal t I n).mul_mem_right a hb⟩

/-- The ring topology whose neighbourhoods of zero have basis `tⁿ I`. -/
@[instance_reducible]
def ringTopology (t : R) (I : Ideal R) : TopologicalSpace R :=
  (filtrationBasis t I).topology

/-- The `(t, I)`-adic topology is compatible with the ring operations. -/
theorem ringTopology_isTopologicalRing (t : R) (I : Ideal R) :
    @IsTopologicalRing R (ringTopology t I) _ :=
  (filtrationBasis t I).toRingFilterBasis.isTopologicalRing

/-- Neighbourhoods are the supersets of the congruence classes modulo `tⁿ I`. -/
theorem ringTopology_nhds (t : R) (I : Ideal R) (a : R) :
    (@nhds R (ringTopology t I) a).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {b | b - a ∈ filtrationIdeal t I n}) :=
  (filtrationBasis t I).hasBasis_nhds a

/-- For the total ideal, the topology is the usual principal adic topology. -/
theorem ringTopology_top (t : R) :
    ringTopology t (⊤ : Ideal R) = (Ideal.span {t}).adicTopology := by
  apply TopologicalSpace.ext_nhds
  intro a
  apply (ringTopology_nhds t ⊤ a).eq_of_same_basis
  simpa only [filtrationIdeal_def, Ideal.smul_eq_mul, Ideal.mul_top,
    Submodule.mem_toAddSubgroup] using
    ((Ideal.span {t}).adic_basis.toRing_subgroups_basis.hasBasis_nhds a)

/-- For the zero ideal the topology is discrete. -/
@[simp]
theorem ringTopology_bot (t : R) : ringTopology t (⊥ : Ideal R) = ⊥ := by
  let := ringTopology t (⊥ : Ideal R)
  have : DiscreteTopology R := discreteTopology_iff_singleton_mem_nhds.mpr fun a ↦
    (ringTopology_nhds t ⊥ a).mem_iff.mpr ⟨0, trivial, by simp [sub_eq_zero]⟩
  exact DiscreteTopology.eq_bot

/-- A residue ring of the filtration, equipped below with the discrete uniformity. -/
-- Code generation of the compatible-family subring needs the quotient carrier to be visible.
@[expose] def Residue (t : R) (I : Ideal R) (n : ℕ) := R ⧸ filtrationIdeal t I n
  deriving CommRing

instance (t : R) (I : Ideal R) (n : ℕ) : UniformSpace (Residue t I n) := ⊥

instance (t : R) (I : Ideal R) (n : ℕ) : DiscreteUniformity (Residue t I n) :=
  ⟨rfl⟩

/-- Reduction to the `n`-th residue ring. -/
def residueMap (t : R) (I : Ideal R) (n : ℕ) : R →+* Residue t I n :=
  Ideal.Quotient.mk _

/-- Reduction sends an element to its quotient class. -/
theorem residueMap_apply (t : R) (I : Ideal R) (n : ℕ) (a : R) :
    residueMap t I n a = Ideal.Quotient.mk (filtrationIdeal t I n) a := by rfl

/-- Reduction identifies two elements exactly when their difference lies in `tⁿ I`. -/
@[simp]
theorem residueMap_eq_iff (t : R) (I : Ideal R) (n : ℕ) (a b : R) :
    residueMap t I n a = residueMap t I n b ↔ a - b ∈ filtrationIdeal t I n :=
  Ideal.Quotient.eq

/-- The kernel of reduction is the corresponding filtration ideal. -/
@[simp]
theorem residueMap_eq_zero_iff (t : R) (I : Ideal R) (n : ℕ) (a : R) :
    residueMap t I n a = 0 ↔ a ∈ filtrationIdeal t I n :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Reduction from a deeper residue ring to a shallower one. -/
def transition (t : R) (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    Residue t I n →+* Residue t I m :=
  Ideal.Quotient.factor (filtrationIdeal_antitone t I h)

@[simp]
theorem transition_residueMap (t : R) (I : Ideal R) {m n : ℕ} (h : m ≤ n) (a : R) :
    transition t I h (residueMap t I n a) = residueMap t I m a := (rfl)

/-- Compatible residues form a subring of the product of the discrete residue rings. -/
def completionSubring (t : R) (I : Ideal R) : Subring (∀ n, Residue t I n) where
  carrier := {x | ∀ (m n : ℕ) (h : m ≤ n), transition t I h (x n) = x m}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy m n h := by simp [hx m n h, hy m n h]
  mul_mem' hx hy m n h := by simp [hx m n h, hy m n h]
  neg_mem' hx m n h := by simp [hx m n h]

/-- Membership in the completion subring is compatibility with every reduction map. -/
@[simp]
theorem mem_completionSubring (t : R) (I : Ideal R) (x : ∀ n, Residue t I n) :
    x ∈ completionSubring t I ↔
      ∀ (m n : ℕ) (h : m ≤ n), transition t I h (x n) = x m := Iff.rfl

/-- The `(t, I)`-adic completion, with its inverse-limit uniformity. -/
abbrev completion (t : R) (I : Ideal R) := ↥(completionSubring t I)

/-- Evaluation at a residue coordinate of the completion. -/
def eval (t : R) (I : Ideal R) (n : ℕ) : completion t I →+* Residue t I n :=
  (Pi.evalRingHom _ n).comp (completionSubring t I).subtype

/-- Coordinates of a completed element are compatible with reduction. -/
@[simp]
theorem transition_eval (t : R) (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : completion t I) : transition t I h (eval t I n x) = eval t I m x :=
  x.property m n h

/-- Two completed elements are equal if all their residues agree. -/
@[ext]
theorem completion_ext {t : R} {I : Ideal R} {x y : completion t I}
    (h : ∀ n, eval t I n x = eval t I n y) : x = y :=
  Subtype.ext (funext h)

/-- Compatible ring maps to the residues assemble into a map to the completion. -/
def lift {S : Type*} [NonAssocSemiring S] (t : R) (I : Ideal R)
    (f : ∀ n, S →+* Residue t I n)
    (hf : ∀ (m n : ℕ) (h : m ≤ n), (transition t I h).comp (f n) = f m) :
    S →+* completion t I :=
  (RingHom.pi f).codRestrict _ fun a m n h ↦ RingHom.congr_fun (hf m n h) a

/-- The assembled map has the specified residue coordinates. -/
@[simp]
theorem eval_lift {S : Type*} [NonAssocSemiring S] (t : R) (I : Ideal R)
    (f : ∀ n, S →+* Residue t I n)
    (hf : ∀ (m n : ℕ) (h : m ≤ n), (transition t I h).comp (f n) = f m)
    (n : ℕ) (a : S) : eval t I n (lift t I f hf a) = f n a := (rfl)

/-- A ring map to the completion is determined by its residue maps. -/
theorem completion_hom_ext {S : Type*} [NonAssocSemiring S] {t : R} {I : Ideal R}
    {f g : S →+* completion t I}
    (h : ∀ n, (eval t I n).comp f = (eval t I n).comp g) : f = g := by
  ext a n
  exact RingHom.congr_fun (h n) a

/-- The canonical map sends an element to its compatible residue classes. -/
def completionMap (t : R) (I : Ideal R) : R →+* completion t I :=
  (RingHom.pi (residueMap t I)).codRestrict _ fun _ ↦ by simp [completionSubring]

@[simp]
theorem eval_completionMap (t : R) (I : Ideal R) (n : ℕ) (a : R) :
    eval t I n (completionMap t I a) = residueMap t I n a := (rfl)

/-- Reduction to every residue ring is surjective. -/
theorem residueMap_surjective (t : R) (I : Ideal R) (n : ℕ) :
    Function.Surjective (residueMap t I n) := Ideal.Quotient.mk_surjective

/-- Every residue class occurs as a coordinate of a completed element. -/
theorem eval_surjective (t : R) (I : Ideal R) (n : ℕ) :
    Function.Surjective (eval t I n) := by
  intro x
  obtain ⟨a, rfl⟩ := residueMap_surjective t I n x
  exact ⟨completionMap t I a, rfl⟩

/-- Exactly the elements divisible into every filtration ideal die in the completion. -/
theorem ker_completionMap (t : R) (I : Ideal R) :
    RingHom.ker (completionMap t I) = ⨅ n, filtrationIdeal t I n := by
  rw [← RingHom.ker_comp_of_injective (completionMap t I)
    (completionSubring t I).subtype_injective]
  exact Ideal.ker_Pi_Quotient_mk (filtrationIdeal t I)

/-- The compatibility equations cut out a closed subring of the product of residues. -/
private theorem isClosed_completionSubring (t : R) (I : Ideal R) :
    IsClosed (completionSubring t I : Set (∀ n, Residue t I n)) := by
  simp only [completionSubring, Set.ofPred_forall]
  exact isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦
    isClosed_eq ((continuous_of_discreteTopology (f := transition t I h)).comp
      (continuous_apply n)) (continuous_apply m)

instance (t : R) (I : Ideal R) : CompleteSpace (completion t I) :=
  (isClosed_completionSubring t I).completeSpace_coe

/-- Evaluation on a completed element is continuous. -/
@[fun_prop]
theorem continuous_eval (t : R) (I : Ideal R) (n : ℕ) : Continuous (eval t I n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- A single residue coordinate suffices to specify a basic neighbourhood in the completion. -/
theorem completion_nhds (t : R) (I : Ideal R) (x : completion t I) :
    (𝓝 x).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {y | eval t I n y = eval t I n x}) := by
  constructor
  intro U
  constructor
  · intro hU
    obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ x U).mp hU
    rw [nhds_pi] at hV
    obtain ⟨s, W, hW, hsub⟩ := Filter.mem_pi'.mp hV
    refine ⟨s.sup id, trivial, fun y hy ↦ hVU (hsub fun n hn ↦ ?_)⟩
    have h := congrArg (transition t I (Finset.le_sup (f := id) hn)) hy
    simp only [transition_eval, id_eq] at h
    have hx : eval t I n x ∈ W n := mem_of_mem_nhds (hW n)
    exact (h.symm ▸ hx : eval t I n y ∈ W n)
  · rintro ⟨n, _, hn⟩
    exact Filter.mem_of_superset
      ((continuous_eval t I n).continuousAt
        (x := x) (U := {eval t I n x}) (by simp)) hn

/-- The original ring is dense in its `(t, I)`-adic completion, even if it is not separated. -/
theorem denseRange_completionMap (t : R) (I : Ideal R) : DenseRange (completionMap t I) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨n, _, hn⟩ := (completion_nhds t I x).mem_iff.mp hU
  obtain ⟨a, ha⟩ := residueMap_surjective t I n (eval t I n x)
  exact ⟨completionMap t I a, hn ha, ⟨a, rfl⟩⟩

/-- The canonical map induces exactly the `(t, I)`-adic topology on the original ring.
It need not be injective. Together with completeness and density, this identifies the
compatible-residue ring as its separated completion. -/
theorem isInducing_completionMap (t : R) (I : Ideal R) :
    @Topology.IsInducing R (completion t I) (ringTopology t I) _ (completionMap t I) := by
  let := ringTopology t I
  rw [isInducing_iff_nhds]
  intro a
  apply (ringTopology_nhds t I a).eq_of_same_basis
  convert (completion_nhds t I (completionMap t I a)).comap (completionMap t I) using 1
  ext n b
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, eval_completionMap, residueMap_eq_iff]

/-- Completion is continuous for the `(t, I)`-adic topology. -/
@[fun_prop]
theorem continuous_completionMap (t : R) (I : Ideal R) :
    Continuous[ringTopology t I, _] (completionMap t I) := by
  let := ringTopology t I
  exact (isInducing_completionMap t I).continuous

private theorem eval_injective_of_constant (t : R) (I : Ideal R)
    (hc : ∀ n, filtrationIdeal t I n = I) : Function.Injective (eval t I 0) := by
  intro x y hxy
  apply completion_ext
  intro n
  have heq (z : Residue t I n) :
      Ideal.quotEquivOfEq ((hc n).trans (hc 0).symm) z =
        transition t I (Nat.zero_le n) z := by
    obtain ⟨a, rfl⟩ := residueMap_surjective t I n z
    rw [transition_residueMap, residueMap_apply, Ideal.quotEquivOfEq_mk,
      residueMap_apply]
  apply (Ideal.quotEquivOfEq ((hc n).trans (hc 0).symm)).injective
  rw [heq, heq, transition_eval, transition_eval]
  exact hxy

/-- With unit parameter `1`, the completion is the quotient `R / I`, not the `I`-adic
completion. The comparison is given by the zeroth residue coordinate. -/
noncomputable def completionOneEquiv (I : Ideal R) : completion (1 : R) I ≃+* R ⧸ I :=
  (RingEquiv.ofBijective (eval 1 I 0)
    ⟨eval_injective_of_constant 1 I (filtrationIdeal_one I), eval_surjective 1 I 0⟩).trans
      (Ideal.quotEquivOfEq (filtrationIdeal_zero 1 I))

/-- The unit-parameter comparison is the zeroth coordinate, with its ideal identified with `I`. -/
theorem completionOneEquiv_apply (I : Ideal R) (x : completion (1 : R) I) :
    completionOneEquiv I x =
      Ideal.quotEquivOfEq (filtrationIdeal_zero 1 I) (eval 1 I 0 x) := by rfl

/-- The unit-parameter comparison sends the canonical image of `a` to its class modulo `I`. -/
@[simp]
theorem completionOneEquiv_completionMap (I : Ideal R) (a : R) :
    completionOneEquiv I (completionMap 1 I a) = Ideal.Quotient.mk I a := by
  rw [completionOneEquiv_apply, eval_completionMap, residueMap_apply,
    Ideal.quotEquivOfEq_mk]

/-- The completion for unit parameter is discrete, as is the quotient `R / I`. -/
instance completionOne_discrete (I : Ideal R) : DiscreteTopology (completion (1 : R) I) :=
  discreteTopology_iff_singleton_mem_nhds.mpr fun x ↦
    (completion_nhds 1 I x).mem_iff.mpr ⟨0, trivial, fun _ hy ↦
      (eval_injective_of_constant 1 I (filtrationIdeal_one I)) hy⟩

/-- For the zero ideal, no elements are identified or added by completion. -/
theorem completionMap_bot_bijective (t : R) :
    Function.Bijective (completionMap t (⊥ : Ideal R)) := by
  have he := eval_injective_of_constant t (⊥ : Ideal R) (filtrationIdeal_bot t)
  constructor
  · intro a b hab
    have h := congrArg (eval t ⊥ 0) hab
    simpa only [eval_completionMap, residueMap_eq_iff, filtrationIdeal_bot,
      Ideal.mem_bot, sub_eq_zero] using h
  · intro x
    obtain ⟨a, ha⟩ := residueMap_surjective t ⊥ 0 (eval t ⊥ 0 x)
    exact ⟨a, he ha⟩

end TauCeti.HenselianApproximation
