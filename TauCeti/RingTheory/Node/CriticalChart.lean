/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.EtaleChart
public import TauCeti.RingTheory.Smooth.CriticalSection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.RingTheory.RingHom.Quotient

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
`Module.Basis.exists_etale_quotient_nodeAlgebra_hom_of_critical` restates the chart in terms of
the hypersurface `W ⧸ (f)` alone: the étale extension of the surface restricts to an étale
neighbourhood of the given point of the hypersurface, which maps étale to the node chart.

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

/-- **A hypersurface at a nondegenerate critical point is étale locally a node.** Let `W` be a
smooth relative surface over `A` whose differentials have a basis, let `f ∈ W`, and let `P` be a
prime of the hypersurface `W ⧸ (f)` at which `f` is critical with nondegenerate Hessian. Then there
are an étale `A`-algebra `A'`, an étale `W ⧸ (f)`-algebra `T` which is an `A'`-algebra compatibly
over `A`, a prime `Q` of `T` lying over `P`, an element `h ∈ A'`, and an étale `A'`-algebra map
`A'[u, v] ⧸ (uv - h) → T` sending both coordinates into `Q`. -/
theorem exists_etale_quotient_nodeAlgebra_hom_of_critical {A W : Type u} [CommRing A]
    [CommRing W] [Algebra A W] [Algebra.Smooth A W] (bW : Basis (Fin 2) W Ω[W⁄A]) (f : W)
    (P : Ideal (W ⧸ Ideal.span {f})) [P.IsPrime]
    (hf : ∀ i, (bW.coord i).compDer (D A W) f ∈ P.comap (Ideal.Quotient.mk _))
    (hdet : (TauCeti.hessian (fun i ↦ (bW.coord i).compDer (D A W)) f).det ∉
      P.comap (Ideal.Quotient.mk _)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (T : Type u) (_ : CommRing T) (_ : Algebra (W ⧸ Ideal.span {f}) T)
      (_ : Algebra.Etale (W ⧸ Ideal.span {f}) T) (_ : Algebra A' T) (_ : Algebra A T)
      (_ : IsScalarTower A (W ⧸ Ideal.span {f}) T) (_ : IsScalarTower A A' T) (Q : Ideal T)
      (_ : Q.IsPrime) (h : A') (φ : TauCeti.NodeAlgebra A' h →ₐ[A'] T),
      P = Q.comap (algebraMap _ T) ∧ φ (TauCeti.NodeAlgebra.coord h 0) ∈ Q ∧
        φ (TauCeti.NodeAlgebra.coord h 1) ∈ Q ∧ φ.toRingHom.Etale := by
  have hf₀ : f ∈ P.comap (Ideal.Quotient.mk _) := by
    simp [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)]
  obtain ⟨A', _, _, _, T, _, _, hWT, _, _, _, _, Q, _, h, s, t, φ, hPQ, hfQ, hs, ht, -,
      hφ₀, hφ₁, hφ⟩ := bW.exists_etale_nodeAlgebra_hom_of_critical f _ hf₀ hf hdet
  -- The étale extension `W → T` of the surface restricts to `W ⧸ (f) → T ⧸ (f)`.
  let I : Ideal T := Ideal.span {algebraMap W T f}
  have hI : (Ideal.span {f}).map (algebraMap W T) = I := by
    rw [Ideal.map_span, Set.image_singleton]
  let ψ : W ⧸ Ideal.span {f} →+* T ⧸ I :=
    (Ideal.quotEquivOfEq hI).toRingHom.comp
      (Ideal.quotientMap _ (algebraMap W T) Ideal.le_comap_map)
  have hψ (w : W) : ψ (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk I (algebraMap W T w) := by
    simp only [ψ, RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, Ideal.quotEquivOfEq_mk]
  -- The prime `Q` descends to `T ⧸ (f)`.
  have hIQ : I ≤ Q := Ideal.span_le.2 (Set.singleton_subset_iff.2 hfQ)
  let : Algebra (W ⧸ Ideal.span {f}) (T ⧸ I) := ψ.toAlgebra
  refine ⟨A', inferInstance, inferInstance, inferInstance, T ⧸ I, inferInstance, inferInstance,
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.isStableUnderBaseChange.quotientMap _ _ (RingHom.etale_algebraMap.2 hWT))
      (RingHom.Etale.of_bijective (Ideal.quotEquivOfEq hI).bijective),
    inferInstance, inferInstance, .of_algebraMap_eq fun r ↦ ?_, inferInstance,
    Q.map (Ideal.Quotient.mk I),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]), h, φ,
    ?_, by simpa [hφ₀] using Ideal.mem_map_of_mem _ hs,
    by simpa [hφ₁] using Ideal.mem_map_of_mem _ ht, hφ⟩
  · rw [RingHom.algebraMap_toAlgebra,
      ← Ideal.Quotient.mk_algebraMap (R₁ := A) (I := Ideal.span {f}), hψ,
      ← IsScalarTower.algebraMap_apply, Ideal.Quotient.mk_algebraMap]
  · refine Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_
    ext w
    rw [hPQ, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, RingHom.algebraMap_toAlgebra, hψ,
      Ideal.mem_quotient_iff_mem hIQ]

end Module.Basis
