/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.EtaleChart
public import TauCeti.RingTheory.Smooth.CriticalSection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Node charts at nondegenerate critical points

Let `W` be a smooth algebra over a ring `A`, with a basis of its differentials consisting of
two elements. At a critical point of `f ∈ W` where the Hessian is nondegenerate, the hypersurface
`f = 0` is étale locally a node `uv = h`, after an étale extension of the base. The tangent
quadratic form need not split over the original residue field, and no characteristic is excluded.

`Module.Basis.exists_etale_nodeAlgebra_hom_of_critical` constructs the chart together with a
point above the original point, and sends both node coordinates into its prime ideal. The
hypersurface equation and its chart have the same principal ideal, so the chart is an étale map
from the node algebra to the quotient by the original equation `f`.

The construction combines `Module.Basis.exists_etale_eq_algebraMap_add_quadratic`, which
centres the function along its critical section, with
`Module.Basis.exists_etale_nodeAlgebra_hom_of_point`, which splits the quadratic part and
constructs its node chart.
An algebraic closure is used only as the value field of a point: all algebra extensions in
the resulting chart are étale and of finite presentation.

## References

* [The Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58):
  families of nodal curves and their étale local structure.
-/

public section

noncomputable section

open KaehlerDifferential MvPolynomial

namespace Module.Basis

universe u

/-- At a nondegenerate critical point of a function on a smooth relative surface, its zero
locus is étale locally a node `uv = h` after an étale extension of the base. The returned prime
lies above the original point, contains the hypersurface equation, and contains the images of
both node coordinates. No splitting assumption on the residue field is required. -/
theorem exists_etale_nodeAlgebra_hom_of_critical {A W : Type u} [CommRing A] [CommRing W]
    [Algebra A W] [Algebra.Smooth A W] (bW : Basis (Fin 2) W Ω[W⁄A]) (f : W)
    (P : Ideal W) [P.IsPrime] (hf₀ : f ∈ P)
    (hf : ∀ i, (bW.coord i).compDer (D A W) f ∈ P)
    (hdet : (TauCeti.hessian (fun i ↦ (bW.coord i).compDer (D A W)) f).det ∉ P) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (T : Type u) (_ : CommRing T) (_ : Algebra W T) (_ : Algebra.Etale W T)
      (_ : Algebra A' T) (_ : Algebra A T) (_ : IsScalarTower A W T)
      (_ : IsScalarTower A A' T) (Q : Ideal T) (_ : Q.IsPrime) (h : A')
      (s t : T) (φ : TauCeti.NodeAlgebra A' h →ₐ[A'] T ⧸ Ideal.span {algebraMap W T f}),
      P = Q.comap (algebraMap W T) ∧ algebraMap W T f ∈ Q ∧
      s ∈ Q ∧ t ∈ Q ∧ s * t - algebraMap A' T h = algebraMap W T f ∧
      φ (TauCeti.NodeAlgebra.coord h 0) = Ideal.Quotient.mk _ s ∧
      φ (TauCeti.NodeAlgebra.coord h 1) = Ideal.Quotient.mk _ t ∧ φ.toRingHom.Etale := by
  obtain ⟨A', _, _, _, W', _, _, _, _, _, _, _, _, bW', P', _, hP', h, a, b, c,
      hbW', -, hquad, hdisc⟩ := bW.exists_etale_eq_algebraMap_add_quadratic f P hf hdet
  let y : Fin 2 → W' := fun i ↦ algebraMap W W' ((bW.coord i).compDer (D A W) f)
  have hy (i : Fin 2) : y i ∈ P' := by
    simpa only [hP', Ideal.mem_comap] using hf i
  -- A geometric point splits the tangent quadratic form, even in characteristic two.
  let K := AlgebraicClosure P'.ResidueField
  have hyK (i : Fin 2) : algebraMap W' K (y i) = 0 := by
    rw [IsScalarTower.algebraMap_apply W' P'.ResidueField K,
      Ideal.algebraMap_residueField_eq_zero.mpr (hy i), map_zero]
  have hdiscK : algebraMap W' K (discrim a b c) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply W' P'.ResidueField K, map_ne_zero]
    exact hdisc
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : K) * Polynomial.X ^ 2 +
      Polynomial.C (algebraMap W' K b) * Polynomial.X + Polynomial.C (algebraMap W' K (a * c)))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; norm_num)
  have hroot : ∃ r : K, r ^ 2 + algebraMap W' K b * r + algebraMap W' K (a * c) = 0 := by
    exact ⟨r, by simpa [Polynomial.IsRoot] using hr⟩
  have hquad' : a * y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2 - algebraMap A' W' (-h) =
      algebraMap W W' f := by
    rw [map_neg, sub_neg_eq_add, hquad]
    exact add_comm _ _
  have hchart := bW'.exists_etale_nodeAlgebra_hom_of_point (hbW' 0) (hbW' 1) a b c (-h) K
    (hyK 0) (hyK 1) hdiscK hroot
  rw [hquad'] at hchart
  obtain ⟨T, _, _, _, _, _, ψ, s, t, φ, hs, ht, heq, hφ₀, hφ₁, hφ⟩ := hchart
  -- Compose the ambient étale extensions and record both compatible base structures.
  let : Algebra W T := ((algebraMap W' T).comp (algebraMap W W')).toAlgebra
  have : IsScalarTower W W' T := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale W T := .comp W W' T
  let : Algebra A T := Algebra.compHom T (algebraMap A W')
  have : IsScalarTower A W' T := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A W T := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A W' T, IsScalarTower.algebraMap_apply A W W',
      IsScalarTower.algebraMap_apply W W' T]
  have : IsScalarTower A A' T := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A W' T, IsScalarTower.algebraMap_apply A A' W',
      IsScalarTower.algebraMap_apply A' W' T]
  let Q := RingHom.ker ψ
  have hQ : P' = Q.comap (algebraMap W' T) := by
    ext x
    simp only [Q, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply W' P'.ResidueField K, map_eq_zero,
      Ideal.algebraMap_residueField_eq_zero]
  have hPQ : P = Q.comap (algebraMap W T) := by
    rw [IsScalarTower.algebraMap_eq W W' T, ← Ideal.comap_comap, ← hQ, ← hP']
  refine ⟨A', inferInstance, inferInstance, inferInstance, T, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q,
    RingHom.ker_isPrime _, -h, s, t, φ, hPQ, ?_,
    RingHom.mem_ker.mpr hs, RingHom.mem_ker.mpr ht, heq, hφ₀, hφ₁, hφ⟩
  simpa only [hPQ, Ideal.mem_comap] using hf₀

end Module.Basis
