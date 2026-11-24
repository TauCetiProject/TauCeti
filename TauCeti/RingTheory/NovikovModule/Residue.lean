/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.Algebra.Torsor.Sigma
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Orbit-invariant and residue gradings of completed combinations

A degree function `d : S → D` on generators cuts the completed module `NovikovModule R F` into
the homogeneous pieces `NovikovModule.gradeBy R F d k`. These pieces are always independent, but
in general they do not span: a completed combination may meet infinitely many degrees, and then
it is not a finite sum of homogeneous combinations. If `d` takes only finitely many values, every
completed combination is the finite sum of its homogeneous components
(`NovikovModule.homogeneousComponent`), so the completion is the internal direct sum of its
homogeneous pieces (`NovikovModule.isInternal_gradeBy`).

For a finite union of torsors `P i` under a group `H`, this applies to any degree that is
constant on each orbit, which then has at most one value per orbit
(`TauCeti.AddTorsor.finite_range_sigma_of_forall_vadd_eq`). Such a grading is moreover
preserved by the Novikov scalar action of *every* series, homogeneous or not
(`NovikovModule.smul_mem_gradeBy_of_forall_vadd_eq`), so the homogeneous pieces are Novikov
submodules (`NovikovModule.novikovGradeBy`) and the completion is their internal direct sum as a
module over the Novikov ring (`NovikovModule.isInternal_novikovGradeBy`).

The main example is the residue of an equivariant degree. If recapping by `h` shifts the degree
by `δ h` for a homomorphism `δ : H →+ D`, then the degree modulo the range of `δ` is constant on
orbits. For capped Hamiltonian Floer generators this
is the Conley–Zehnder grading modulo twice the first Chern numbers of spherical classes: modulo
`2N` for minimal Chern number `N` in the monotone case, and the integer grading itself when the
first Chern class vanishes on spheres. In contrast, the integer grading has infinite range as
soon as `δ ≠ 0`, and then the homogeneous integer pieces need not span the completion.

## Main definitions

* `TauCeti.NovikovModule.novikovGradeBy`: for an orbit-invariant degree, the homogeneous piece of
  degree `k` as a submodule over the Novikov ring.

## Main results

* `TauCeti.NovikovModule.iSupIndep_of_forall_mem_iff`,
  `TauCeti.NovikovModule.isInternal_of_forall_mem_iff`: independence of the homogeneous pieces,
  and the internal direct sum decomposition for a degree with finite range, over any ring of
  scalars for which the pieces are submodules.
* `TauCeti.NovikovModule.iSupIndep_gradeBy`: the homogeneous pieces are independent over the
  ground ring, for every degree function.
* `TauCeti.NovikovModule.mem_iSup_gradeBy_iff_finite`,
  `TauCeti.NovikovModule.isInternal_iff_of_forall_mem_iff`,
  `TauCeti.NovikovModule.isInternal_gradeBy_iff`: for an arbitrary degree, a completed combination
  is a finite sum of homogeneous combinations exactly when it meets finitely many degrees, so the
  completion is the internal direct sum of its homogeneous pieces, over any ring of scalars for
  which they are submodules, exactly when every completed combination does.
* `TauCeti.NovikovModule.range_ofFinsupp_le_iSup_gradeBy`: every finite combination is a finite
  sum of homogeneous combinations.
* `TauCeti.NovikovModule.smul_mem_gradeBy_of_forall_vadd_eq`: every Novikov series preserves the
  homogeneous pieces of an orbit-invariant degree.
* `TauCeti.NovikovModule.isInternal_novikovGradeBy`: the completion is the direct sum of its
  orbit-invariant homogeneous pieces as a Novikov module.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the grading of Floer complexes over Novikov rings.
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

open Set
open scoped DirectSum

variable {R S D : Type*}

section Semiring

variable [Semiring R]

section Generators

variable {F : S → ℝ} {d : S → D}

section Decomposition

variable {Λ : Type*} [Semiring Λ] [Module Λ (NovikovModule R F)]
  {A : D → Submodule Λ (NovikovModule R F)}

/-- Homogeneous pieces of distinct degrees are independent. This holds for any ring of scalars
`Λ` for which the pieces are submodules, such as the ground ring or, for an orbit-invariant
degree, the Novikov ring. -/
theorem iSupIndep_of_forall_mem_iff (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k) :
    iSupIndep A := by
  intro k
  rw [Submodule.disjoint_def]
  intro a hak ha
  -- The homogeneous component of degree `k` vanishes on the pieces of other degrees, hence on
  -- their supremum, but it is the identity on the piece of degree `k`.
  have h0 : homogeneousComponent R F d k a = 0 := by
    refine Submodule.iSup_induction _ (motive := fun x => homogeneousComponent R F d k x = 0) ha
      (fun j x hx => ?_) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    refine Submodule.iSup_induction _ (motive := fun x => homogeneousComponent R F d k x = 0) hx
      (fun hjk y hy => homogeneousComponent_eq_zero_of_mem_gradeBy ((hA j y).1 hy) hjk)
      (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  rwa [homogeneousComponent_of_mem_gradeBy ((hA k a).1 hak)] at h0

/-- The homogeneous pieces of the completed combinations are independent, for every degree
function. -/
theorem iSupIndep_gradeBy (d : S → D) : iSupIndep (gradeBy R F d) :=
  iSupIndep_of_forall_mem_iff fun _ _ => Iff.rfl

/-- A completed combination is a finite sum of homogeneous combinations exactly when its nonzero
coefficients occur at generators of only finitely many degrees. -/
theorem mem_iSup_gradeBy_iff_finite {a : NovikovModule R F} :
    a ∈ ⨆ k, gradeBy R F d k ↔ (d '' Function.support a.val).Finite := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine Submodule.iSup_induction (motive := fun b => (d '' Function.support b.val).Finite) _ ha
      (fun k b hb => (finite_singleton k).subset ?_) (by simp) fun b c hb hc => ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact mem_gradeBy_iff.1 hb s hs
    · exact (hb.union hc).subset
        ((image_mono (Function.support_add _ _)).trans (image_union _ _ _).le)
  · rw [← sum_homogeneousComponent (T := ha.toFinset) fun s hs => ha.mem_toFinset.2 ⟨s, hs, rfl⟩]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.mem_iSup_of_mem k (homogeneousComponent_mem_gradeBy d k a)

/-- The homogeneous component of degree `k` of a sum of homogeneous combinations, one in each
piece, is the summand of degree `k`. -/
theorem homogeneousComponent_coeAddMonoidHom [DecidableEq D]
    (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k) (f : ⨁ k, A k) (k : D) :
    homogeneousComponent R F d k (DirectSum.coeAddMonoidHom A f) = f k := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hjk : j = k
    · subst hjk
      rw [DirectSum.of_eq_same, homogeneousComponent_of_mem_gradeBy ((hA _ _).1 x.property)]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk),
        homogeneousComponent_eq_zero_of_mem_gradeBy ((hA _ _).1 x.property) hjk,
            ZeroMemClass.coe_zero]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply, AddMemClass.coe_add]

/-- The homogeneous combinations span the completed module exactly when every completed
combination meets only finitely many degrees. -/
theorem iSup_gradeBy_eq_top_iff :
    ⨆ k, gradeBy R F d k = ⊤ ↔
      ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite := by
  simp only [Submodule.eq_top_iff', mem_iSup_gradeBy_iff_finite]

/-- Every finite combination is a finite sum of homogeneous combinations. -/
theorem range_ofFinsupp_le_iSup_gradeBy :
    LinearMap.range (ofFinsupp F) ≤ ⨆ k, gradeBy R F d k := fun _ ha =>
  mem_iSup_gradeBy_iff_finite.2 ((mem_range_ofFinsupp_iff.1 ha).image d)

/-- The completed module is the internal direct sum of its homogeneous pieces exactly when every
completed combination meets only finitely many degrees, over any ring of scalars `Λ` for which the
pieces are submodules. -/
theorem isInternal_iff_of_forall_mem_iff [DecidableEq D]
    (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k) :
    DirectSum.IsInternal A ↔ ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite := by
  refine ⟨fun h a => ?_, fun h => ⟨fun f g hfg => DirectSum.ext fun k => Subtype.ext ?_,
    fun a => ?_⟩⟩
  · -- `a` is a finite sum of homogeneous combinations.
    obtain ⟨f, rfl⟩ := h.2 a
    refine mem_iSup_gradeBy_iff_finite.1 ?_
    induction f using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of k x =>
      rw [DirectSum.coeAddMonoidHom_of]
      exact Submodule.mem_iSup_of_mem k ((hA k _).1 x.property)
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
  · -- The summands are recovered as homogeneous components.
    rw [← homogeneousComponent_coeAddMonoidHom hA, ← homogeneousComponent_coeAddMonoidHom hA,
      hfg]
  · -- `a` is the sum of its finitely many homogeneous components.
    refine ⟨∑ k ∈ (h a).toFinset, DirectSum.of (fun k => A k) k
      ⟨homogeneousComponent R F d k a, (hA k _).2 (homogeneousComponent_mem_gradeBy d k a)⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact sum_homogeneousComponent fun s hs => (h a).mem_toFinset.2 ⟨s, hs, rfl⟩

/-- For a degree with finitely many values, the completed module is the internal direct sum of
its homogeneous pieces, over any ring of scalars `Λ` for which the pieces are submodules. -/
theorem isInternal_of_forall_mem_iff [DecidableEq D] (hd : (range d).Finite)
    (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k) : DirectSum.IsInternal A :=
  (isInternal_iff_of_forall_mem_iff hA).2 fun _ => hd.subset (image_subset_range d _)

/-- For a degree with finitely many values, the completed module is the internal direct sum of
its homogeneous pieces. -/
theorem isInternal_gradeBy [DecidableEq D] (hd : (range d).Finite) :
    DirectSum.IsInternal (gradeBy R F d) :=
  isInternal_of_forall_mem_iff hd fun _ _ => Iff.rfl

/-- The completed module is the internal direct sum of its homogeneous pieces exactly when every
completed combination meets only finitely many degrees. -/
theorem isInternal_gradeBy_iff [DecidableEq D] :
    DirectSum.IsInternal (gradeBy R F d) ↔
      ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite :=
  isInternal_iff_of_forall_mem_iff fun _ _ => Iff.rfl

end Decomposition

end Generators

section Orbit

variable {H ι : Type*} [AddGroup H] [Finite ι] {P : ι → Type*} [∀ i, AddTorsor H (P i)]
  {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
  {d : (Σ i, P i) → D} (hd : ∀ i (h : H) (p : P i), d ⟨i, h +ᵥ p⟩ = d ⟨i, p⟩)

include hd in
/-- Every Novikov series, homogeneous or not, preserves the homogeneous pieces of a degree that
is constant on orbits. -/
theorem smul_mem_gradeBy_of_forall_vadd_eq (b : NovikovSeries R H N) {k : D}
    {a : NovikovModule R F} (ha : a ∈ gradeBy R F d k) :
    letI := module (R := R) hF
    b • a ∈ gradeBy R F d k := by
  let := module (R := R) hF
  -- Relabel the degrees injectively in the free additive group on `D`, so that `d` shifts by the
  -- zero homomorphism and every series has degree zero for `smul_mem_gradeBy`.
  have h := smul_mem_gradeBy hF (0 : H →+ FreeAddGroup D) (d := FreeAddGroup.of ∘ d)
    (fun i h p => by simp [hd]) (j := 0) (b := b)
    (NovikovSeries.mem_gradeBy_iff.2 fun _ _ => rfl)
    (gradeBy_le_gradeBy_comp FreeAddGroup.of k ha)
  rw [zero_add] at h
  exact mem_gradeBy_iff.2 fun s hs => FreeAddGroup.of_injective (mem_gradeBy_iff.1 h s hs)

/-- For a degree that is constant on orbits, the completed combinations of degree `k` form a
submodule over the Novikov ring. -/
def novikovGradeBy (k : D) :
    letI := module (R := R) hF
    Submodule (NovikovSeries R H N) (NovikovModule R F) :=
  letI := module (R := R) hF
  { carrier := gradeBy R F d k
    zero_mem' := (gradeBy R F d k).zero_mem
    add_mem' := (gradeBy R F d k).add_mem
    smul_mem' := fun b _ ha => smul_mem_gradeBy_of_forall_vadd_eq hF hd b ha }

/-- Membership in the Novikov submodule of degree `k` is homogeneity of degree `k`. -/
@[simp]
theorem mem_novikovGradeBy {k : D} {a : NovikovModule R F} :
    a ∈ novikovGradeBy hF hd k ↔ a ∈ gradeBy R F d k :=
  Iff.rfl

/-- For a degree that is constant on orbits, the completed module of a finite union of torsors
is the internal direct sum of its homogeneous pieces, as a module over the Novikov ring. -/
theorem isInternal_novikovGradeBy [DecidableEq D] :
    letI := module (R := R) hF
    DirectSum.IsInternal (novikovGradeBy (R := R) hF hd) :=
  letI := module (R := R) hF
  isInternal_of_forall_mem_iff (AddTorsor.finite_range_sigma_of_forall_vadd_eq hd)
    fun _ _ => Iff.rfl

end Orbit

end Semiring

end TauCeti.NovikovModule
