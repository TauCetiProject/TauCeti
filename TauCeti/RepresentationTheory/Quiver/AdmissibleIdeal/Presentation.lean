/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Subalgebra.Nilpotent
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Kernel
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows
public import TauCeti.RingTheory.Semisimple.BasicAlgebra
import TauCeti.RingTheory.Idempotents.LinearIndependent

/-!
# Bound-quiver presentations of basic algebras

Let `A` be an algebra with a nilpotent two-sided ideal `J`, a complete family of orthogonal
idempotents `e : Q → A`, and for each arrow `a : i ⟶ j` of a quiver on `Q` an element `f a` of
the corner `e j * A * e i`. These data define an algebra map `kQ → A` from the path algebra
(`TauCeti.PathAlgebra.liftAlgHomOfArrows`). This file gives the two criteria that make it a
*bound-quiver presentation*, a surjection with admissible kernel, so that `A ≃ kQ ⧸ I` with
`I` admissible:

* it is **surjective** once the vertex idempotents span `A ⧸ J` and, for all vertices `i` and
  `j`, the arrows `i ⟶ j` span the `(j, i)`-corner of the first layer `J ⧸ J ^ 2`;
* its kernel is **admissible** once the arrows lie in `J`, the vertex idempotents are nonzero,
  and the arrows `i ⟶ j` stay linearly independent in `A ⧸ J ^ 2`.

Both conditions hold when `J` is the Jacobson radical of a finite-dimensional basic algebra over
an algebraically closed field: the Wedderburn blocks of `A ⧸ J` are copies of the field, their
units lift to orthogonal idempotents of `A`, and the arrows are chosen as lifts of a basis of each
corner of `J ⧸ J ^ 2`. This is Gabriel's theorem that such an algebra is a bound quiver algebra.

## Main results

* `TauCeti.PathAlgebra.liftAlgHomOfArrows_surjective`: the generation criterion.
* `TauCeti.PathAlgebra.isAdmissibleIdeal_ker_liftAlgHomOfArrows`: the admissibility criterion.
* `TauCeti.IsBasic.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker`: **Gabriel's
  presentation theorem** for a finite-dimensional basic algebra over an algebraically closed
  field.

## Implementation notes

The quiver built in the proof has the Wedderburn blocks of `A ⧸ J` as vertices, and as arrows
`i ⟶ j` the indices of a basis of the `(j, i)`-corner of `J ⧸ J ^ 2`; this is how the ordinary
quiver of `A` is defined. The theorem asserts only the existence of some finite quiver: neither
that identification nor the description of the arrow counts by `Ext¹` between simple modules is
stated here.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter II, §3, Theorem 3.7.
* P. Gabriel, *Indecomposable representations II*, Symposia Mathematica XI (1973), 81--104.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

namespace PathAlgebra

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] {A : Type*} [Ring A]
variable (e : Q → A) (he : CompleteOrthogonalIdempotents e)
variable (f : ∀ {i j : Q}, (i ⟶ j) → A)
variable (hl : ∀ {i j : Q} (a : i ⟶ j), e j * f a = f a)
variable (hr : ∀ {i j : Q} (a : i ⟶ j), f a * e i = f a)
variable (J : Ideal A) [J.IsTwoSided]

section Generation

variable {k : Type w} [CommSemiring k] [Algebra k A]

/-- **Generation criterion for a bound-quiver presentation.** Let `J` be a nilpotent two-sided
ideal. If the vertex idempotents span `A ⧸ J`, and for all vertices `i` and `j` the arrows
`i ⟶ j` span the `(j, i)`-corner of the first layer `J ⧸ J ^ 2`, then the algebra map from the
path algebra is surjective. -/
theorem liftAlgHomOfArrows_surjective (hJ : IsNilpotent J)
    (hquot : Submodule.span k (Set.range fun i => Ideal.Quotient.mk J (e i)) = ⊤)
    (hlayer : ∀ i j : Q, ∀ x ∈ J, Ideal.Quotient.mk (J ^ 2) (e j * x * e i) ∈
      Submodule.span k (Set.range fun a : i ⟶ j => Ideal.Quotient.mk (J ^ 2) (f a))) :
    Function.Surjective (liftAlgHomOfArrows k e he f hl hr) := by
  set F := liftAlgHomOfArrows k e he f hl hr
  apply F.surjective_of_nilpotent_ideal J hJ
  · intro y
    have hy : y ∈ Submodule.span k (Set.range fun i => Ideal.Quotient.mk J (e i)) := by
      rw [hquot]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy
    refine ⟨∑ i, c i • vertexIdempotent k i, ?_⟩
    simp [F, ← hc, Ideal.Quotient.mkₐ_eq_mk]
  · intro x hx
    have hxcut : x = ∑ j, ∑ i, e j * x * e i := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, one_mul, mul_one]
    rw [hxcut]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => ?_
    -- Lift the class of the cut to a combination of arrows; the error lies in `J ^ 2`.
    have hmem := hlayer i j x hx
    have hrange : (Set.range fun a : i ⟶ j => Ideal.Quotient.mk (J ^ 2) (f a)) =
        (Ideal.Quotient.mkₐ k (J ^ 2)).toLinearMap '' Set.range (fun a : i ⟶ j => f a) := by
      ext
      simp [Ideal.Quotient.mkₐ_eq_mk]
    rw [hrange, ← Submodule.map_span] at hmem
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hmem
    have hzF : z ∈ F.range.toSubmodule := by
      refine Submodule.span_le.mpr ?_ hz
      rintro _ ⟨a, rfl⟩
      exact ⟨ofArrow a, by simp [F, ofArrow_eq_ofPath]⟩
    refine Submodule.mem_sup.mpr ⟨z, hzF, e j * x * e i - z, ?_, by abel⟩
    exact (Submodule.restrictScalars_mem k _ _).mpr
      (Ideal.Quotient.eq.mp (by simpa using hzx.symm))

end Generation

section Admissible

variable {k : Type w} [Field k] [Algebra k A]

/-- **Admissibility criterion for a bound-quiver presentation.** Let `J` be a nilpotent two-sided
ideal containing the arrow values, and let the vertex idempotents be nonzero. If for all vertices
`i` and `j` the classes of the arrows `i ⟶ j` in `A ⧸ J ^ 2` are linearly independent, then the
kernel of the algebra map from the path algebra is admissible. -/
theorem isAdmissibleIdeal_ker_liftAlgHomOfArrows (hJ : IsNilpotent J) (hne : ∀ i, e i ≠ 0)
    (harrows : ∀ {i j : Q} (a : i ⟶ j), f a ∈ J)
    (hind : ∀ i j : Q, LinearIndependent k fun a : i ⟶ j => Ideal.Quotient.mk (J ^ 2) (f a)) :
    IsAdmissibleIdeal (RingHom.ker (liftAlgHomOfArrows k e he f hl hr).toRingHom) := by
  classical
  have hJ2 : J ^ 2 ≤ J := Ideal.pow_le_self two_ne_zero
  -- A nonzero idempotent is not nilpotent, so it does not lie in `J`.
  have hnotMem (i : Q) : e i ∉ J := fun hmem => by
    obtain ⟨n, hn⟩ := hJ
    exact hne i ((he.idem i).eq_zero_of_isNilpotent
      ⟨n, by simpa [hn] using Ideal.pow_mem_pow hmem n⟩)
  refine (liftAlgHomOfArrows k e he f hl hr).isAdmissibleIdeal_ker J hJ
    (fun i j a => by simpa [ofArrow_eq_ofPath] using harrows a) ?_
  rw [← linearIndependent_equiv shortPathTwoEquiv]
  have hfun : (fun p : ShortPath Q 2 => Ideal.Quotient.mk (J ^ 2)
      (liftAlgHomOfArrows k e he f hl hr (ofPath p.1))) ∘ shortPathTwoEquiv =
      Sum.elim (fun i => Ideal.Quotient.mk (J ^ 2) (e i))
        (fun a : Σ i j : Q, i ⟶ j => Ideal.Quotient.mk (J ^ 2) (f a.2.2)) := by
    ext (i | ⟨i, j, a⟩) <;> simp
  rw [hfun]
  -- The vertex classes, the arrow classes, and the disjointness of their spans.
  have hvert (I : Ideal A) [I.IsTwoSided] (hI : I ≤ J) :
      LinearIndependent k fun i => Ideal.Quotient.mk I (e i) :=
    (he.toOrthogonalIdempotents.map (Ideal.Quotient.mk I)).linearIndependent fun i h =>
      hnotMem i (hI (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have harrowIndependent : LinearIndependent k fun a : (Σ i j : Q, i ⟶ j) =>
      Ideal.Quotient.mk (J ^ 2) (f a.2.2) :=
    (he.toOrthogonalIdempotents.map (Ideal.Quotient.mk (J ^ 2))).linearIndependent_sigma
      (fun i j a => Ideal.Quotient.mk (J ^ 2) (f a))
      (fun i j a => by rw [Function.comp_apply, ← map_mul, hl a])
      (fun i j a => by rw [Function.comp_apply, ← map_mul, hr a]) hind
  refine (hvert _ hJ2).sum_type harrowIndependent ?_
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy
  let ψ := (Ideal.Quotient.factorₐ k hJ2).toLinearMap
  have hψ : Submodule.span k (Set.range fun a : Σ i j : Q, i ⟶ j =>
      Ideal.Quotient.mk (J ^ 2) (f a.2.2)) ≤ LinearMap.ker ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    simpa [ψ, Ideal.Quotient.eq_zero_iff_mem] using harrows a.2.2
  have hc := Fintype.linearIndependent_iff.mp (hvert J le_rfl) c (by simpa [ψ] using hψ hy')
  simp [hc]

end Admissible

end PathAlgebra

/-- **Gabriel's presentation theorem for basic algebras.** A finite-dimensional basic algebra over
an algebraically closed field is a quotient of the path algebra of a finite quiver by an
admissible ideal: there is a surjective algebra map `kQ → A` whose kernel is admissible. -/
theorem IsBasic.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker {k : Type w} {A : Type u}
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] (hA : IsBasic A) :
    ∃ (Q : Type) (_ : Quiver.{0} Q) (_ : Finite Q) (_ : ∀ i j : Q, Finite (i ⟶ j))
      (F : pathAlgebra k Q →ₐ[k] A),
      Function.Surjective F ∧ IsAdmissibleIdeal (RingHom.ker F.toRingHom) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hJ : IsNilpotent (Ring.jacobson A) := IsSemiprimaryRing.isNilpotent
  obtain ⟨n, e, he, hne, hquot⟩ := hA.exists_completeOrthogonalIdempotents (k := k)
  -- The arrows `i ⟶ j` index a basis of the `(j, i)`-corner of `J ⧸ J ^ 2`.
  let W (i j : Fin n) : Submodule k (A ⧸ Ring.jacobson A ^ 2) :=
    ((Ring.jacobson A).restrictScalars k).map
      ((Ideal.Quotient.mkₐ k (Ring.jacobson A ^ 2)).toLinearMap ∘ₗ
        LinearMap.mulLeftRight k (e j, e i))
  let : Quiver.{0} (Fin n) := ⟨fun i j => Fin (Module.finrank k (W i j))⟩
  have hlift (i j : Fin n) (t : i ⟶ j) : ∃ x ∈ Ring.jacobson A,
      Ideal.Quotient.mk (Ring.jacobson A ^ 2) (e j * x * e i) = Module.finBasis k (W i j) t := by
    obtain ⟨x, hx, hxt⟩ := Submodule.mem_map.mp (Module.finBasis k (W i j) t).2
    exact ⟨x, hx, by simpa using hxt⟩
  choose x hxJ hx using hlift
  let f : ∀ {i j : Fin n}, (i ⟶ j) → A := fun {i j} t => e j * x i j t * e i
  have hl {i j : Fin n} (t : i ⟶ j) : e j * f t = f t := by
    simp only [f, ← mul_assoc, (he.idem j).eq]
  have hr {i j : Fin n} (t : i ⟶ j) : f t * e i = f t := by
    simp only [f, mul_assoc, (he.idem i).eq]
  have hbasis (i j : Fin n) : (fun t : i ⟶ j => Ideal.Quotient.mk (Ring.jacobson A ^ 2) (f t)) =
      (W i j).subtype ∘ Module.finBasis k (W i j) := funext (hx i j)
  refine ⟨Fin n, inferInstance, inferInstance,
    fun i j => inferInstanceAs (Finite (Fin (Module.finrank k (W i j)))),
    liftAlgHomOfArrows k e he f hl hr, ?_, ?_⟩
  · refine liftAlgHomOfArrows_surjective e he f hl hr _ hJ hquot fun i j y hy => ?_
    rw [hbasis, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
      Submodule.range_subtype]
    exact Submodule.mem_map_of_mem
      (f := (Ideal.Quotient.mkₐ k (Ring.jacobson A ^ 2)).toLinearMap ∘ₗ
        LinearMap.mulLeftRight k (e j, e i)) hy
  · refine isAdmissibleIdeal_ker_liftAlgHomOfArrows e he f hl hr _ hJ hne
      (fun {i j} t => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hxJ i j t))) fun i j => ?_
    rw [hbasis]
    exact (Module.finBasis k (W i j)).linearIndependent.map' _ (Submodule.ker_subtype _)

end TauCeti
