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
completed combination is the finite sum of its homogeneous parts
(`NovikovModule.gradeProj`), so the completion is the internal direct sum of its homogeneous
pieces (`NovikovModule.isInternal_gradeBy`).

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

* `TauCeti.NovikovModule.gradeProj`: the homogeneous part of degree `k` of a completed
  combination.
* `TauCeti.NovikovModule.novikovGradeBy`: for an orbit-invariant degree, the homogeneous piece of
  degree `k` as a submodule over the Novikov ring.

## Main results

* `TauCeti.NovikovModule.iSupIndep_of_forall_mem_iff`,
  `TauCeti.NovikovModule.isInternal_of_forall_mem_iff`: independence of the homogeneous pieces,
  and the internal direct sum decomposition for a degree with finite range, over any ring of
  scalars for which the pieces are submodules.
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

section Proj

variable [DecidableEq D]

variable (R F) in
/-- The homogeneous part of degree `k` of a completed combination: the coefficients at generators
of degree `k`, with all other coefficients set to zero. -/
def gradeProj (d : S → D) (k : D) : NovikovModule R F →ₗ[R] NovikovModule R F where
  toFun a := ⟨fun s => if d s = k then a.val s else 0, mem_iff.2 fun C => (finite_gt a C).subset
    fun s hs => ⟨fun h => hs.1 (by simp [h]), hs.2⟩⟩
  map_add' a b := by
    ext s
    by_cases h : d s = k <;> simp [h]
  map_smul' r a := by
    ext s
    by_cases h : d s = k <;> simp [h]

/-- The coefficients of the homogeneous part of degree `k`. -/
@[simp]
theorem gradeProj_val (d : S → D) (k : D) (a : NovikovModule R F) (s : S) :
    (gradeProj R F d k a).val s = if d s = k then a.val s else 0 :=
  (rfl)

/-- The homogeneous part of degree `k` is homogeneous of degree `k`. -/
theorem gradeProj_mem_gradeBy (d : S → D) (k : D) (a : NovikovModule R F) :
    gradeProj R F d k a ∈ gradeBy R F d k :=
  mem_gradeBy_iff.2 fun s hs => by
    by_contra h
    exact hs (by simp [h])

/-- A homogeneous combination of degree `k` is its own homogeneous part of degree `k`. -/
theorem gradeProj_eq_self_of_mem_gradeBy {k : D} {a : NovikovModule R F}
    (ha : a ∈ gradeBy R F d k) : gradeProj R F d k a = a := by
  ext s
  by_cases h : d s = k
  · simp [h]
  · simp [h, val_eq_zero_of_mem_gradeBy ha h]

/-- A homogeneous combination of degree `j` has no homogeneous part of another degree `k`. -/
theorem gradeProj_eq_zero_of_mem_gradeBy {j k : D} (hjk : j ≠ k) {a : NovikovModule R F}
    (ha : a ∈ gradeBy R F d j) : gradeProj R F d k a = 0 := by
  ext s
  by_cases h : d s = k
  · simp [h, val_eq_zero_of_mem_gradeBy ha (h.trans_ne hjk.symm)]
  · simp [h]

/-- If every degree lies in the finite set `T`, a completed combination is the sum of its
homogeneous parts of degrees in `T`. -/
theorem sum_gradeProj (T : Finset D) (hT : ∀ s, d s ∈ T) (a : NovikovModule R F) :
    ∑ k ∈ T, gradeProj R F d k a = a := by
  ext s
  simp only [Submodule.coe_sum, Finset.sum_apply, gradeProj_val, Finset.sum_ite_eq, hT, ite_true]

end Proj

section Decomposition

variable {Λ : Type*} [Semiring Λ] [Module Λ (NovikovModule R F)]
  {A : D → Submodule Λ (NovikovModule R F)}

/-- Homogeneous pieces of distinct degrees are independent. This holds for any ring of scalars
`Λ` for which the pieces are submodules, such as the ground ring or, for an orbit-invariant
degree, the Novikov ring. -/
theorem iSupIndep_of_forall_mem_iff (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k) :
    iSupIndep A := by
  classical
  intro k
  rw [Submodule.disjoint_def]
  intro a hak ha
  -- The homogeneous part of degree `k` vanishes on the pieces of other degrees, hence on their
  -- supremum, but it is the identity on the piece of degree `k`.
  have h0 : gradeProj R F d k a = 0 := by
    refine Submodule.iSup_induction _ (motive := fun x => gradeProj R F d k x = 0) ha
      (fun j x hx => ?_) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    refine Submodule.iSup_induction _ (motive := fun x => gradeProj R F d k x = 0) hx
      (fun hjk y hy => gradeProj_eq_zero_of_mem_gradeBy hjk ((hA j y).1 hy)) (map_zero _)
      (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  rwa [gradeProj_eq_self_of_mem_gradeBy ((hA k a).1 hak)] at h0

/-- The homogeneous part of degree `k` of a sum of homogeneous combinations, one in each piece,
is the summand of degree `k`. -/
theorem gradeProj_coeAddMonoidHom [DecidableEq D] (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k)
    (f : ⨁ k, A k) (k : D) :
    gradeProj R F d k (DirectSum.coeAddMonoidHom A f) = f k := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hjk : j = k
    · subst hjk
      rw [DirectSum.of_eq_same, gradeProj_eq_self_of_mem_gradeBy ((hA _ _).1 x.2)]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk),
        gradeProj_eq_zero_of_mem_gradeBy hjk ((hA _ _).1 x.2), ZeroMemClass.coe_zero]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply, AddMemClass.coe_add]

/-- For a degree with finitely many values, the completed module is the internal direct sum of
its homogeneous pieces, over any ring of scalars `Λ` for which the pieces are submodules. -/
theorem isInternal_of_forall_mem_iff [DecidableEq D] (hd : (range d).Finite)
    (hA : ∀ k a, a ∈ A k ↔ a ∈ gradeBy R F d k) : DirectSum.IsInternal A := by
  refine ⟨fun f g hfg => DirectSum.ext fun k => Subtype.ext ?_, fun a => ?_⟩
  · rw [← gradeProj_coeAddMonoidHom hA, ← gradeProj_coeAddMonoidHom hA, hfg]
  · -- `a` is the sum of its finitely many homogeneous parts.
    refine ⟨∑ k ∈ hd.toFinset, DirectSum.of (fun k => A k) k
      ⟨gradeProj R F d k a, (hA k _).2 (gradeProj_mem_gradeBy d k a)⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact sum_gradeProj hd.toFinset (fun s => hd.mem_toFinset.2 ⟨s, rfl⟩) a

/-- For a degree with finitely many values, the completed module is the internal direct sum of
its homogeneous pieces. -/
theorem isInternal_gradeBy [DecidableEq D] (hd : (range d).Finite) :
    DirectSum.IsInternal (gradeBy R F d) :=
  isInternal_of_forall_mem_iff hd fun _ _ => Iff.rfl

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
