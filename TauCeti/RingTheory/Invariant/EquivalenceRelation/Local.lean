/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.Algebra.Module.Submodule.Union
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Basis

/-!
# Equivalence relations with a local ring of invariants

Let `s = algebraMap A B` and `t : A →+* B` define an equivalence relation `Spec B ⇉ Spec A`
(`RingHom.IsSpecEquivRel`) with `B` finite free over `A` through `s`, and suppose that its ring of
invariants `C = {a : s a = t a}` is a local ring with infinite residue field. This file proves that
there are elements `aᵢ ∈ A` whose images `t aᵢ` form a basis of `B` over `A`
(`RingHom.IsSpecEquivRel.exists_basis_eq_apply`). By `RingHom.IsSpecEquivRel.basis` and
`RingHom.IsSpecEquivRel.tensorProductEquiv`, the `aᵢ` then form a basis of `A` over `C`, and
`A ⊗[C] A ≅ B`: the quotient map `Spec A ⟶ Spec C` is finite free, and the relation is its
kernel pair. This is the local case of the quotient of an affine scheme by a finite locally free
equivalence relation (SGA 3, Exposé V, Théorème 4.1), for local rings of invariants with infinite
residue field.

The elements are found by general position. Since `A` is integral over `C` and the points of
`Spec C` are the orbits of the relation, the maximal ideals of `A` form a single orbit, which is
finite because `B` is finite over `A` (`RingHom.IsSpecEquivRel.finite_maximalSpectrum`). Fix a
basis of `B` over `A`. For each maximal ideal `q` of `A`, reducing coordinates modulo `q` gives a
map from `B` to `κ(q)ⁿ`, and the images of the `t a` span `κ(q)ⁿ`, because `t(A)` spans `B`
(`RingHom.IsSpecEquivRel.span_range_eq_top`). The `aᵢ` are chosen one at a time: the elements `a`
for which the image of `t a` lies in the span of the images of the earlier `t aⱼ` form a proper
`C`-submodule of `A` for each `q`, and a module over a local ring with infinite residue field is
not a finite union of proper submodules
(`Submodule.exists_forall_notMem_of_forall_ne_top_of_isLocalRing`). The resulting matrix of
coordinates has a determinant that lies in no maximal ideal of `A`, so it is a unit.

## Main results

* `RingHom.IsSpecEquivRel.finite_maximalSpectrum`: if the ring of invariants is local, `A` has
  finitely many maximal ideals.
* `RingHom.IsSpecEquivRel.exists_basis_eq_apply`: if the ring of invariants is local with infinite
  residue field, some basis of `B` over `A` consists of elements `t aᵢ`.
* `RingHom.IsSpecEquivRel.free_of_isLocalRing`, `RingHom.IsSpecEquivRel.finite_of_isLocalRing` and
  `RingHom.IsSpecEquivRel.exists_tensorProductEquiv_of_isLocalRing`: then `A` is finite free over
  the ring of invariants `C`, and `A ⊗[C] A ≅ B`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

universe u

open IsLocalRing TensorProduct

namespace RingHom.IsSpecEquivRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (h : (algebraMap A B).IsSpecEquivRel t)
include h

/-- **`A` is semilocal over a local ring of invariants.** If `B` is finite projective over `A` and
the ring of invariants `C = {a : s a = t a}` is local, then `A` has finitely many maximal ideals:
they all lie over the maximal ideal of `C`, so they form a single orbit of the relation, and this
orbit is finite because `B` is finite over `A`. -/
theorem finite_maximalSpectrum [Module.Finite A B] [Module.Projective A B]
    [IsLocalRing ((algebraMap A B).eqLocus t)] : _root_.Finite (MaximalSpectrum A) := by
  set C := (algebraMap A B).eqLocus t
  have := h.isIntegral
  -- every maximal ideal of `A` lies over the maximal ideal of `C`
  have hmax (q : MaximalSpectrum A) : q.toPrimeSpectrum.comap C.subtype = closedPoint C :=
    PrimeSpectrum.ext (eq_maximalIdeal (Ideal.IsMaximal.under C q.asIdeal))
  rcases isEmpty_or_nonempty (MaximalSpectrum A) with hA | ⟨⟨q₀⟩⟩
  · infer_instance
  -- so each is related to a fixed `q₀` by one of the finitely many primes of `B` over `q₀`
  have hF := (Algebra.QuasiFinite.finite_primesOver (S := B) q₀.asIdeal).image (Ideal.comap t)
  have hsub (q : MaximalSpectrum A) : q.asIdeal ∈ Ideal.comap t '' q₀.asIdeal.primesOver B := by
    obtain ⟨r, hr, hr'⟩ := h.comap_subtype_eqLocus_eq_iff.mp ((hmax q₀).trans (hmax q).symm)
    exact ⟨r.asIdeal, ⟨r.isPrime, ⟨congr(($hr).asIdeal).symm⟩⟩, congr(($hr').asIdeal)⟩
  have := hF.to_subtype
  exact Finite.of_injective (fun q ↦ (⟨q.asIdeal, hsub q⟩ : Ideal.comap t '' _))
    fun q q' hqq' ↦ MaximalSpectrum.ext congr(($hqq').1)

variable {ι : Type*} (b : Module.Basis ι A B)

omit h in
-- the coordinates in `b`, reduced modulo the prime `q` of `A`
private noncomputable def coordMod (q : Ideal A) [q.IsPrime] : B →ₗ[A] ι → q.ResidueField :=
  LinearMap.pi fun i ↦ Algebra.linearMap A q.ResidueField ∘ₗ b.coord i

omit h in
private theorem coordMod_apply (q : Ideal A) [q.IsPrime] (y : B) (i : ι) :
    coordMod b q y i = algebraMap A q.ResidueField (b.repr y i) :=
  rfl

omit h in
-- the elements `x` of `A` for which the reduction of `t x` modulo `q` lies in `U`, a submodule
-- over the ring of invariants
private noncomputable def preimageSubmodule (q : Ideal A) [q.IsPrime]
    (U : Submodule q.ResidueField (ι → q.ResidueField)) :
    Submodule ((algebraMap A B).eqLocus t) A where
  carrier := {x | coordMod b q (t x) ∈ U}
  add_mem' hx hy := by simpa using add_mem hx hy
  zero_mem' := by simp
  smul_mem' c x hx := by
    -- `t (c x) = s c * t x`, since `c` is an invariant
    have hc : t (c • x) = (c : A) • t x := by
      rw [Subring.smul_def, smul_eq_mul, map_mul, ← mem_eqLocus.mp c.2, Algebra.smul_def]
    simpa [hc] using U.smul_of_tower_mem (c : A) hx

omit h in
-- general position: `k ≤ |ι|` elements `aⱼ` whose `t aⱼ` are independent modulo every maximal
-- ideal of `A`, chosen one at a time outside finitely many proper submodules
private theorem exists_linearIndependent_coordMod [Fintype ι]
    [IsLocalRing ((algebraMap A B).eqLocus t)]
    [Infinite (ResidueField ((algebraMap A B).eqLocus t))] [_root_.Finite (MaximalSpectrum A)]
    (hspan : ∀ q : MaximalSpectrum A,
      Submodule.span q.asIdeal.ResidueField (Set.range fun x ↦ coordMod b q.asIdeal (t x)) = ⊤)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ∃ a : Fin k → A, ∀ q : MaximalSpectrum A,
      LinearIndependent q.asIdeal.ResidueField fun j ↦ coordMod b q.asIdeal (t (a j)) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun q ↦ linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih (by omega)
    -- the span of the first `k` vectors is proper, so the `x` with `t x` in it are a proper
    -- submodule
    let U (q : MaximalSpectrum A) := Submodule.span q.asIdeal.ResidueField
      (Set.range fun j ↦ coordMod b q.asIdeal (t (a j)))
    have hU (q : MaximalSpectrum A) : preimageSubmodule (t := t) b q.asIdeal (U q) ≠ ⊤ := by
      intro htop
      have hle : Module.finrank q.asIdeal.ResidueField (U q) ≤ k :=
        (finrank_range_le_card fun j ↦ coordMod b q.asIdeal (t (a j))).trans_eq (Fintype.card_fin k)
      have heq : U q = ⊤ := eq_top_iff.mpr <| (hspan q).ge.trans <| Submodule.span_le.mpr <| by
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ preimageSubmodule (t := t) b q.asIdeal (U q) := htop ▸ Submodule.mem_top
        exact hx
      rw [heq, finrank_top, Module.finrank_fintype_fun_eq_card] at hle
      omega
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top_of_isLocalRing _ hU
    refine ⟨Fin.cons x a, fun q ↦ ?_⟩
    have := (ha q).finCons (hx q)
    convert this using 1
    ext j : 1
    cases j using Fin.cases <;> simp

/-- **A basis of `B` from the base, over a local ring of invariants.** Let `Spec B ⇉ Spec A` be an
equivalence relation with `B` finite free over `A` through `s`, whose ring of invariants
`C = {a : s a = t a}` is a local ring with infinite residue field. Then some basis of `B` over `A`
consists of images `t aᵢ` of elements `aᵢ ∈ A`. -/
theorem exists_basis_eq_apply [Module.Finite A B] [Module.Free A B]
    [IsLocalRing ((algebraMap A B).eqLocus t)]
    [Infinite (ResidueField ((algebraMap A B).eqLocus t))] :
    ∃ (b : Module.Basis (Fin (Module.finrank A B)) A B) (a : Fin (Module.finrank A B) → A),
      ∀ i, b i = t (a i) := by
  have : Nontrivial A := ⟨⟨1, 0, fun h1 ↦
    one_ne_zero (Subtype.ext h1 : (1 : (algebraMap A B).eqLocus t) = 0)⟩⟩
  have := h.finite_maximalSpectrum
  let b₀ := Module.finBasis A B
  -- modulo each maximal ideal `q`, the vectors `t x` span `κ(q)ⁿ`, since `t(A)` spans `B`
  have hspan (q : MaximalSpectrum A) :
      Submodule.span q.asIdeal.ResidueField
        (Set.range fun x ↦ coordMod b₀ q.asIdeal (t x)) = ⊤ := by
    have hmem (y : B) : coordMod b₀ q.asIdeal y ∈ Submodule.span q.asIdeal.ResidueField
        (Set.range fun x ↦ coordMod b₀ q.asIdeal (t x)) := by
      have := Submodule.mem_map_of_mem (f := coordMod b₀ q.asIdeal)
        (h.span_range_eq_top ▸ Submodule.mem_top : y ∈ Submodule.span A (Set.range t))
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact Submodule.span_le_restrictScalars A _ _ this
    rw [eq_top_iff, ← (Pi.basisFun q.asIdeal.ResidueField _).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]
    convert hmem (b₀ i) using 1
    ext j
    simp [coordMod_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  obtain ⟨a, ha⟩ := exists_linearIndependent_coordMod b₀ hspan (Module.finrank A B) (by simp)
  -- the determinant of the coordinates of the `t aᵢ` lies in no maximal ideal
  have hdet : IsUnit (b₀.det (t ∘ a)) := by
    by_contra hnu
    obtain ⟨q, hq, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    have hcol : ((b₀.toMatrix (t ∘ a)).map (algebraMap A q.ResidueField)).col =
        fun j ↦ coordMod b₀ q (t (a j)) := by
      ext j i
      simp [Matrix.col_apply, coordMod_apply, Module.Basis.toMatrix_apply]
    have hu := Matrix.linearIndependent_col_iff_isUnit.mp (hcol ▸ ha ⟨q, hq⟩)
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    refine hu.ne_zero ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Module.Basis.det_apply,
      Ideal.algebraMap_residueField_eq_zero]
    exact hmem
  obtain ⟨hli, hsp⟩ := (b₀.is_basis_iff_det).mpr hdet
  exact ⟨.mk hli hsp.ge, a, fun i ↦ by simp⟩

variable [Module.Finite A B] [Module.Free A B] [IsLocalRing ((algebraMap A B).eqLocus t)]
  [Infinite (ResidueField ((algebraMap A B).eqLocus t))]

/-- **The quotient map is free.** If `B` is finite free over `A` and the ring of invariants `C` is
local with infinite residue field, then `A` is a free `C`-module. -/
theorem free_of_isLocalRing : Module.Free ((algebraMap A B).eqLocus t) A :=
  have ⟨b, _, hb⟩ := h.exists_basis_eq_apply
  .of_basis (h.basis b hb)

/-- **The quotient map is finite.** If `B` is finite free over `A` and the ring of invariants `C`
is local with infinite residue field, then `A` is a finite `C`-module. -/
theorem finite_of_isLocalRing : Module.Finite ((algebraMap A B).eqLocus t) A :=
  have ⟨b, _, hb⟩ := h.exists_basis_eq_apply
  .of_basis (h.basis b hb)

/-- **The relation is the kernel pair of the quotient map.** If `B` is finite free over `A` and
the ring of invariants `C` is local with infinite residue field, then `x ⊗ y ↦ s x * t y` is an
isomorphism of `A`-algebras `A ⊗[C] A ≃ₐ[A] B`. -/
theorem exists_tensorProductEquiv_of_isLocalRing :
    ∃ e : A ⊗[(algebraMap A B).eqLocus t] A ≃ₐ[A] B,
      ∀ x y, e (x ⊗ₜ y) = algebraMap A B x * t y :=
  have ⟨b, _, hb⟩ := h.exists_basis_eq_apply
  ⟨h.tensorProductEquiv b hb, h.tensorProductEquiv_tmul b hb⟩

end RingHom.IsSpecEquivRel
