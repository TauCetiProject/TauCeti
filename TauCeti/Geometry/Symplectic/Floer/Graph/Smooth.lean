/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Graph.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Floer
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Graph
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Gromov's structure of the Floer equation is a smooth almost complex structure

Let `ω` be a fibrewise nondegenerate two-form on a manifold `M` modelled on a finite-dimensional
space, such as a closed symplectic manifold, let `K = K_s ds + K_t dt` be a Hamiltonian
perturbation whose components are jointly `C^(n+1)` on `(ℝ × ℝ) × M`, and let `J` be a jointly
`Cⁿ` domain-dependent almost complex structure on `M`, a
`TauCeti.ContMDiffAlmostComplexStructureFamily` over `ℝ × ℝ`. In
`TauCeti.Geometry.Symplectic.Floer.Graph.Manifold`, Gromov's structure

`J_K(z, x)(ξ, v) = (j ξ, J(z, x) (v - X_K ξ) + X_K (j ξ))`

of the Floer equation (`TauCeti.SmoothTwoForm.floerGraphAlmostComplex`) is defined one tangent
space of `(ℝ × ℝ) × M` at a time. This file shows that it is a `Cⁿ` almost complex structure on the
product manifold `(ℝ × ℝ) × M`, that is, a `Cⁿ` section of the endomorphism bundle of its whole
tangent bundle.

* The Hamiltonian one-form `X_K(z, x) = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` is a native `Cⁿ` Hom section
  from the tangent bundle of `ℝ × ℝ` to the tangent bundle of `M` over `(ℝ × ℝ) × M`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianOneFormSection`), since the Hamiltonian
  vector fields of a jointly `C^(n+1)` family are jointly `Cⁿ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField_uncurry`).
* Gromov's graph structure along it, with the standard structure of `ℝ × ℝ` horizontally
  (`TauCeti.DomainDependentHomSection.graphStructure`), is the `Cⁿ` structure
  `TauCeti.SmoothTwoForm.IsNondegenerate.floerGraphStructure`, and at each point it is
  `floerGraphAlmostComplex` for the frozen structures `J(z, ·)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.almostComplexStructureAt_floerGraphStructure`).
* Consequently a map `u : ℝ × ℝ → M` solves the Floer equation `(du - X_K)^{0,1} = 0` at `z`
  exactly when its graph is pseudoholomorphic at `z` for this `Cⁿ` structure
  (`exists_hasMFDerivAt_graph_isComplexLinearMap_floerGraphStructure_iff`), and a map into the fibre
  over a domain point `z` is pseudoholomorphic for it exactly when it is pseudoholomorphic for the
  structure `J(z, ·)` frozen at `z`
  (`exists_hasMFDerivAt_prodMk_isComplexLinearMap_floerGraphStructure_iff`).

So the graphs of Floer solutions are pseudoholomorphic curves for a `Cⁿ` almost complex structure
on the manifold `(ℝ × ℝ) × M`, and maps into the fibre over `z` are pseudoholomorphic for it exactly
when they are for `J(z, ·)`. Applying compactness and bubbling for such curves to the graphs also
needs a taming form, Gromov's form `Ω_c` closed on `(ℝ × ℝ) × M`, which is not treated here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  graph construction.
-/

public noncomputable section

open Bundle Function
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {n : ℕ∞} {Ks Kt : ℝ × ℝ → M → ℝ}

/-- The Hamiltonian one-form `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` of a jointly `C^(n+1)`
perturbation is jointly `Cⁿ` as a section of the bundle of homomorphisms from the tangent bundle of
`ℝ × ℝ` to the tangent bundle of `M` over `(ℝ × ℝ) × M`. -/
theorem contMDiff_hamiltonianOneForm (hω : ω.IsNondegenerate)
    (hKs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (uncurry Ks))
    (hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (uncurry Kt)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) ((𝓘(ℝ, ℝ × ℝ).prod I).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] E)) n
      (fun q : (ℝ × ℝ) × M ↦ TotalSpace.mk' ((ℝ × ℝ) →L[ℝ] E)
        (E := fun q : (ℝ × ℝ) × M ↦ horizontalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) q →L[ℝ]
          verticalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) q) q
        (ω.hamiltonianOneForm Ks Kt q.1 q.2)) := by
  refine (TauCeti.contMDiff_hom_bundle_iff
    (E₁ := horizontalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))
    (E₂ := verticalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) _).2 ?_
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hproj := contMDiff_proj (n := n) (F := ℝ × ℝ) (IB := 𝓘(ℝ, ℝ × ℝ).prod I)
    (horizontalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))
  -- The domain vector `ξ`, read in the model tangent bundle of `ℝ × ℝ`.
  have hlift := Pullback.contMDiff_lift (n := n) (F := ℝ × ℝ) (E := TangentSpace 𝓘(ℝ, ℝ × ℝ))
    (ContMDiffMap.fst : ContMDiffMap (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ × ℝ)
      ((ℝ × ℝ) × M) (ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞))
    (contMDiff_fst (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) (M := ℝ × ℝ) (N := M))
  have hξ : ContMDiff ((𝓘(ℝ, ℝ × ℝ).prod I).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ) n
      (fun p : TotalSpace (ℝ × ℝ) (horizontalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) ↦
        (p.snd : ℝ × ℝ)) :=
    ((contMDiff_snd_tangentBundle_modelSpace (ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ)).comp hlift).congr fun p ↦
      (Pullback.lift_snd _ p).symm
  -- The two terms `ξ₁ X_{K_s}` and `ξ₂ X_{K_t}` of `X_K ξ`, as fields of tangent vectors of `M`.
  have hs : ContMDiff ((𝓘(ℝ, ℝ × ℝ).prod I).prod 𝓘(ℝ, ℝ × ℝ)) I.tangent n
      (fun p : TotalSpace (ℝ × ℝ) (horizontalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) ↦
        TotalSpace.mk' E p.proj.2
          ((p.snd : ℝ × ℝ).1 • ω.hamiltonianVectorField (Ks p.proj.1) p.proj.2)) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff.contMDiff.comp hξ).smul_totalSpace
      ((hω.contMDiff_hamiltonianVectorField_uncurry hn hKs).comp hproj)
  have ht : ContMDiff ((𝓘(ℝ, ℝ × ℝ).prod I).prod 𝓘(ℝ, ℝ × ℝ)) I.tangent n
      (fun p : TotalSpace (ℝ × ℝ) (horizontalTangentBundle I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) ↦
        TotalSpace.mk' E p.proj.2
          ((p.snd : ℝ × ℝ).2 • ω.hamiltonianVectorField (Kt p.proj.1) p.proj.2)) :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff.contMDiff.comp hξ).smul_totalSpace
      ((hω.contMDiff_hamiltonianVectorField_uncurry hn hKt).comp hproj)
  refine (Pullback.contMDiff_iff (ContMDiffMap.snd : ContMDiffMap (𝓘(ℝ, ℝ × ℝ).prod I) I
    ((ℝ × ℝ) × M) M ((⊤ : ℕ∞) : WithTop ℕ∞))
    contMDiff_snd).2 ⟨hproj, (hs.add_sectionAlong ht).congr fun p ↦ ?_⟩
  exact congrArg (TotalSpace.mk' E p.proj.2)
    (hamiltonianOneForm_apply ω Ks Kt p.proj.1 p.proj.2 p.snd)

/-- The **Hamiltonian one-form** `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` of a jointly `C^(n+1)`
perturbation, as a native `Cⁿ` Hom section from the tangent bundle of `ℝ × ℝ` to the tangent bundle
of `M` over `(ℝ × ℝ) × M`. -/
def hamiltonianOneFormSection (hω : ω.IsNondegenerate)
    (hKs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (uncurry Ks))
    (hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (uncurry Kt)) :
    DomainDependentHomSection I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n :=
  ⟨fun q ↦ ω.hamiltonianOneForm Ks Kt q.1 q.2, hω.contMDiff_hamiltonianOneForm hKs hKt⟩

variable (hω : ω.IsNondegenerate)
  (hKs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (uncurry Ks))
  (hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (uncurry Kt))

@[simp]
theorem hamiltonianOneFormSection_tangentHom_apply (q : (ℝ × ℝ) × M)
    (ξ : TangentSpace 𝓘(ℝ, ℝ × ℝ) q.1) :
    (hω.hamiltonianOneFormSection hKs hKt).tangentHom q ξ =
      ω.hamiltonianOneForm Ks Kt q.1 q.2 ξ := by
  rw [DomainDependentHomSection.tangentHom_apply]
  -- The section is `ContMDiffSection.mk` of `fun q ↦ ω.hamiltonianOneForm Ks Kt q.1 q.2`. Its
  -- fibres `ℝ × ℝ →L[ℝ] TangentSpace I q.2` are the pulled-back Hom fibres only definitionally,
  -- so `ContMDiffSection.coeFn_mk` does not typecheck as a rewrite here, and `rfl` evaluates it.
  rfl

variable (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n)

/-- **Gromov's structure of the Floer equation**, as a `Cⁿ` almost complex structure on the product
manifold `(ℝ × ℝ) × M`: at `(z, x)` it sends `(ξ, v)` to `(j ξ, J(z, x) (v - X_K ξ) + X_K (j ξ))`,
for the standard structure `j` of `ℝ × ℝ`. -/
def floerGraphStructure : ContMDiffAlmostComplexStructure (𝓘(ℝ, ℝ × ℝ).prod I) n ((ℝ × ℝ) × M) :=
  (hω.hamiltonianOneFormSection hKs hKt).graphStructure (planeDomainStructure n) J

/-- The `Cⁿ` structure `floerGraphStructure` acts on each tangent space of `(ℝ × ℝ) × M` as
Gromov's structure `floerGraphAlmostComplex` for the structures `J(z, ·)` frozen at the domain
points. -/
@[simp]
theorem floerGraphStructure_apply (q : (ℝ × ℝ) × M) (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) q) :
    hω.floerGraphStructure hKs hKt J q v = (Manifold.tangentSpaceProdEquiv q).symm
      (ω.floerGraphAlmostComplex (fun z x ↦ (J.freeze z).almostComplexStructureAt x) Ks Kt q
        (Manifold.tangentSpaceProdEquiv q v)) := by
  rw [floerGraphStructure, DomainDependentHomSection.graphStructure_apply,
    hamiltonianOneFormSection_tangentHom_apply, hamiltonianOneFormSection_tangentHom_apply]
  -- The tangent space of `ℝ × ℝ` is `ℝ × ℝ`, so `floerGraphAlmostComplex_apply` applies to the
  -- components of `v`; `rw` does not see through this identification of types.
  refine congrArg (Manifold.tangentSpaceProdEquiv q).symm (Eq.trans ?_
    (floerGraphAlmostComplex_apply ω _ Ks Kt q (Manifold.tangentSpaceProdEquiv q v)).symm)
  refine Prod.ext (planeDomainStructure_apply n q.1 _) ?_
  dsimp only
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, J.freeze_apply]
  exact congrArg (_ + ·) (congrArg _ (planeDomainStructure_apply n q.1 _))

/-- At each point, the `Cⁿ` structure `floerGraphStructure` is Gromov's structure
`floerGraphAlmostComplex` for the structures `J(z, ·)` frozen at the domain points. -/
@[simp]
theorem almostComplexStructureAt_floerGraphStructure (q : (ℝ × ℝ) × M) :
    (hω.floerGraphStructure hKs hKt J).almostComplexStructureAt q =
      ω.floerGraphAlmostComplex (fun z x ↦ (J.freeze z).almostComplexStructureAt x) Ks Kt q := by
  ext v
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, floerGraphStructure_apply]
  exact (Manifold.tangentSpaceProdEquiv_symm_apply q _).trans
    (congrArg _ (Manifold.tangentSpaceProdEquiv_apply q v))

variable {hω hKs hKt J}

/-- **Gromov's graph construction for the smooth structure.** A map `u : ℝ × ℝ → M` solves the
Floer equation `(du - X_K)^{0,1} = 0` for the structures `J(z, ·)` at `z` exactly when its graph
`w ↦ (w, u w)` has a manifold derivative at `z` which is complex linear from the standard structure
of `ℝ × ℝ` to the `Cⁿ` structure `floerGraphStructure`. -/
theorem exists_hasMFDerivAt_graph_isComplexLinearMap_floerGraphStructure_iff {u : ℝ × ℝ → M}
    {z : ℝ × ℝ} :
    (∃ Γ' : ℝ × ℝ →L[ℝ] TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) (z, u z),
        HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) (fun w ↦ (w, u w)) z Γ' ∧
          IsComplexLinearMap (AlmostComplexStructure.product ℝ)
            ((hω.floerGraphStructure hKs hKt J).almostComplexStructureAt (z, u z))
            (Γ' : ℝ × ℝ →ₗ[ℝ] TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) (z, u z))) ↔
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z ∧
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          ((J.freeze z).almostComplexStructureAt (u z))
          (ω.perturbedMFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] TangentSpace I (u z)) := by
  rw [almostComplexStructureAt_floerGraphStructure]
  exact exists_hasMFDerivAt_graph_isComplexLinearMap_iff

/-- **Vertical maps for the smooth structure.** A map `y ↦ (z, g y)` into the fibre over a fixed
domain point `z` has a manifold derivative complex linear into `floerGraphStructure` exactly when
`g` has a manifold derivative complex linear into the structure `J(z, ·)` frozen at `z`. -/
theorem exists_hasMFDerivAt_prodMk_isComplexLinearMap_floerGraphStructure_iff
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    {j' : (y : N) → AlmostComplexStructure (TangentSpace I' y)} {g : N → M} {z : ℝ × ℝ}
    {y : N} :
    (∃ f' : TangentSpace I' y →L[ℝ] TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) (z, g y),
        HasMFDerivAt I' (𝓘(ℝ, ℝ × ℝ).prod I) (fun y ↦ (z, g y)) y f' ∧
          IsComplexLinearMap (j' y)
            ((hω.floerGraphStructure hKs hKt J).almostComplexStructureAt (z, g y))
            (f' : TangentSpace I' y →ₗ[ℝ] TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) (z, g y))) ↔
      ∃ g' : TangentSpace I' y →L[ℝ] TangentSpace I (g y),
        HasMFDerivAt I' I g y g' ∧
          IsComplexLinearMap (j' y) ((J.freeze z).almostComplexStructureAt (g y))
            (g' : TangentSpace I' y →ₗ[ℝ] _) := by
  rw [almostComplexStructureAt_floerGraphStructure]
  exact exists_hasMFDerivAt_prodMk_isComplexLinearMap_iff

end TauCeti.SmoothTwoForm.IsNondegenerate
