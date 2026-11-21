/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Chart
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Reparametrizing inhomogeneous terms along the domain

Let `ν` be an inhomogeneous term for an almost complex structure `j` on a manifold `P` and a
domain-dependent almost complex structure `J` on a manifold `M`. A `C^{n+1}` map `g : Q → P`
whose differential intertwines an almost complex structure `j'` on `Q` with `j` pulls `ν` back to
an inhomogeneous term `g^* ν` for `j'` and the reparametrized family `J ∘ g`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.comp`): at `(x, y)` it is `ν(g x, y) ∘ dg_x`.
This is how the data of the inhomogeneous Cauchy–Riemann equation transform under a holomorphic
change of the domain, for instance a biholomorphism of a Riemann surface.

Read in charts, both transports are the identity: if `φ'` is a chart of `Q` and `φ` a chart of `P`
with `g ∘ φ'⁻¹ = φ⁻¹`, such as `φ' = g ≫ φ` for a diffeomorphism `g`, then `J ∘ g` read in `φ'`
is `J` read in `φ`, and `g^* ν` read in `φ'` is `ν` read in `φ` wherever `φ'⁻¹` is
differentiable.

## Main declarations

* `TauCeti.InhomogeneousTerm.comp`: the reparametrization `g^* ν`, with
  `TauCeti.InhomogeneousTerm.comp_val_tangentHom`; it is linear in `ν`
  (`TauCeti.InhomogeneousTerm.comp_zero`, `comp_add`, `comp_smul`, `comp_neg`, `comp_sub`).
* `TauCeti.InhomogeneousTerm.chartTerm_comp`: transport in charts; the family counterpart is
  `TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_comp`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M EP HP P EQ HQ Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]
  {n : ℕ∞}

namespace InhomogeneousTerm

variable [FiniteDimensional ℝ EP] [FiniteDimensional ℝ EQ]
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}

/-- The field `(x, y) ↦ ν(g x, y) ∘ dg_x` underlying the reparametrization of an inhomogeneous
term along `g`. -/
private def compField (A : DomainDependentHomSection I M IP P n) (g : Q → P) (q : Q × M) :
    TangentSpace IQ q.1 →L[ℝ] TangentSpace I q.2 :=
  A.tangentHom (g q.1, q.2) ∘L mfderiv IQ IP g q.1

/-- The field `(x, y) ↦ ν(g x, y) ∘ dg_x` is a jointly `Cⁿ` Hom section when `g` is `C^{n+1}`. -/
private theorem contMDiff_compField (A : DomainDependentHomSection I M IP P n) {g : Q → P}
    (hg : ContMDiff IQ IP (n + 1) g) :
    ContMDiff (IQ.prod I) ((IQ.prod I).prod 𝓘(ℝ, EQ →L[ℝ] E)) n
      (fun q : Q × M ↦ TotalSpace.mk' (EQ →L[ℝ] E)
        (E := fun q : Q × M ↦ horizontalTangentBundle I M IQ Q q →L[ℝ]
          verticalTangentBundle I M IQ Q q) q (compField A g q)) := by
  refine (TauCeti.contMDiff_hom_bundle_iff (E₁ := horizontalTangentBundle I M IQ Q)
    (E₂ := verticalTangentBundle I M IQ Q) (compField A g)).2 ?_
  have hg' : ContMDiff IQ IP n g := hg.of_le le_self_add
  -- Push a horizontal vector at `(x, y)` forward along `dg_x` to a horizontal vector at
  -- `(g x, y)`.
  have hT : ContMDiff (IQ.prod 𝓘(ℝ, EQ)) (IP.prod 𝓘(ℝ, EP)) n (tangentMap IQ IP g) :=
    hg.contMDiff_tangentMap le_rfl
  have hS : ContMDiff ((IQ.prod I).prod 𝓘(ℝ, EQ)) ((IP.prod I).prod 𝓘(ℝ, EP)) n
      (fun p : TotalSpace EQ (horizontalTangentBundle I M IQ Q) ↦
        (⟨(g p.proj.1, p.proj.2), mfderiv IQ IP g p.proj.1 p.snd⟩ :
          TotalSpace EP (horizontalTangentBundle I M IP P))) := by
    refine (Bundle.Pullback.contMDiff_iff
      (ContMDiffMap.fst : C^∞⟮IP.prod I, P × M; IP, P⟯) contMDiff_fst).2 ⟨?_, ?_⟩
    · exact (hg'.comp (contMDiff_fst.comp (contMDiff_proj _))).prodMk
        (contMDiff_snd.comp (contMDiff_proj _))
    · exact hT.comp (Bundle.Pullback.contMDiff_lift
        (ContMDiffMap.fst : C^∞⟮IQ.prod I, Q × M; IQ, Q⟯) contMDiff_fst)
  -- Apply `A` there and read the result as a vector tangent to `M`.
  have hA := (TauCeti.contMDiff_hom_bundle_iff (E₁ := horizontalTangentBundle I M IP P)
    (E₂ := verticalTangentBundle I M IP P) A.tangentHom).1 A.contMDiff_tangentHom
  have hV := (Bundle.Pullback.contMDiff_lift
    (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) contMDiff_snd).comp (hA.comp hS)
  exact (Bundle.Pullback.contMDiff_iff
    (ContMDiffMap.snd : C^∞⟮IQ.prod I, Q × M; I, M⟯) contMDiff_snd).2
      ⟨contMDiff_proj _, hV⟩

/-- **Reparametrization along the domain.** For a `C^{n+1}` map `g : Q → P` whose differential
intertwines an almost complex structure `j'` on `Q` with `j`, the pullback `g^* ν` of an
inhomogeneous term for `(j, J)` is an inhomogeneous term for `(j', J ∘ g)`: at `(x, y)` it is
`ν(g x, y) ∘ dg_x`. The map `g` is given as a `Cⁿ` map, as the family `J ∘ g` requires, together
with its `C^{n+1}` regularity. -/
def comp (ν : InhomogeneousTerm j J) (j' : ContMDiffAlmostComplexStructure IQ n Q)
    (g : C^n⟮IQ, Q; IP, P⟯) (hg : ContMDiff IQ IP (n + 1) g)
    (hgj : ∀ x v, mfderiv IQ IP g x (j' x v) = j (g x) (mfderiv IQ IP g x v)) :
    InhomogeneousTerm j' (J.comp g) :=
  ⟨⟨compField ν.val g, contMDiff_compField ν.val hg⟩, (mem_inhomogeneousTerms _ _ _).2 fun q ↦ by
    apply isComplexAntilinear_of_apply
    intro v
    have h := ν.tangentHom_apply_j (g q.1, q.2) (mfderiv IQ IP g q.1 v)
    rw [ContMDiffAlmostComplexStructureFamily.tangentEndomorphism_apply] at h
    -- The goal is stated in the horizontal fibre of `Q × M` pulled back from `Q`, a type synonym
    -- of `TangentSpace IQ q.1`; `rw` cannot see through the synonym to match these lemmas (as in
    -- `InhomogeneousTerm.tangentHom_apply_j`).
    erw [ContMDiffAlmostComplexStructure.horizontalEndomorphism_apply,
      ContMDiffAlmostComplexStructureFamily.comp_toEndomorphism_apply]
    exact (congrArg (ν.val.tangentHom (g q.1, q.2)) (hgj q.1 v)).trans h⟩

variable (ν : InhomogeneousTerm j J) (j' : ContMDiffAlmostComplexStructure IQ n Q)
  (g : C^n⟮IQ, Q; IP, P⟯) (hg : ContMDiff IQ IP (n + 1) g)
  (hgj : ∀ x v, mfderiv IQ IP g x (j' x v) = j (g x) (mfderiv IQ IP g x v))

/-- The reparametrized term at `(x, y)`, evaluated on a tangent vector `v`, is
`ν(g x, y)(dg_x v)`. -/
@[simp]
theorem comp_val_tangentHom_apply (q : Q × M) (v : TangentSpace IQ q.1) :
    (ν.comp j' g hg hgj).val.tangentHom q v =
      ν.val.tangentHom (g q.1, q.2) (mfderiv IQ IP g q.1 v) := by
  rw [DomainDependentHomSection.tangentHom_apply]
  -- The reparametrized section is the field `compField` by definition.
  rfl

/-- The reparametrized term at `(x, y)` is `ν(g x, y) ∘ dg_x`. -/
theorem comp_val_tangentHom (q : Q × M) :
    (ν.comp j' g hg hgj).val.tangentHom q =
      ν.val.tangentHom (g q.1, q.2) ∘L mfderiv IQ IP g q.1 := by
  ext v
  exact comp_val_tangentHom_apply ν j' g hg hgj q v

/-- The reparametrization of the zero term is zero. -/
@[simp]
theorem comp_zero : (0 : InhomogeneousTerm j J).comp j' g hg hgj = 0 :=
  ext_tangentHom fun q v ↦ by simp

/-- Reparametrization is additive. -/
@[simp]
theorem comp_add (μ : InhomogeneousTerm j J) :
    (ν + μ).comp j' g hg hgj = ν.comp j' g hg hgj + μ.comp j' g hg hgj :=
  ext_tangentHom fun q v ↦ by simp

/-- Reparametrization commutes with scalar multiplication. -/
@[simp]
theorem comp_smul (c : ℝ) : (c • ν).comp j' g hg hgj = c • ν.comp j' g hg hgj :=
  ext_tangentHom fun q v ↦ by simp

/-- Reparametrization commutes with negation. -/
@[simp]
theorem comp_neg : (-ν).comp j' g hg hgj = -ν.comp j' g hg hgj :=
  ext_tangentHom fun q v ↦ by simp

/-- Reparametrization commutes with subtraction. -/
@[simp]
theorem comp_sub (μ : InhomogeneousTerm j J) :
    (ν - μ).comp j' g hg hgj = ν.comp j' g hg hgj - μ.comp j' g hg hgj :=
  ext_tangentHom fun q v ↦ by simp

/-- **Transport in charts.** Let `φ'` be a chart of `Q` and `φ` a chart of `P`, both with values
in `ℂ`, with `g ∘ φ'⁻¹ = φ⁻¹`. At a point `z` where `φ'⁻¹` is differentiable, the reparametrized
term `g^* ν` read in `φ'` is `ν` read in `φ`. -/
theorem chartTerm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ' : OpenPartialHomeomorph Q ℂ} {φ : OpenPartialHomeomorph P ℂ} (hφ : g ∘ φ'.symm = φ.symm)
    (ψ : OpenPartialHomeomorph M G) {z : ℂ} (hz : MDifferentiableAt 𝓘(ℝ, ℂ) IQ φ'.symm z) :
    (ν.comp j' g hg hgj).chartTerm φ' ψ z = ν.chartTerm φ ψ z := by
  have hgd : MDifferentiableAt IQ IP g (φ'.symm z) :=
    (hg (φ'.symm z)).mdifferentiableAt (by simp)
  funext v
  have hd1 : mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ) =
      mfderiv IQ IP g (φ'.symm z) (mfderiv 𝓘(ℝ, ℂ) IQ φ'.symm z (1 : ℂ)) := by
    rw [← hφ]
    exact mfderiv_comp_apply z hgd hz _
  -- The tangent spaces at `g (φ'⁻¹ z)` and at `φ⁻¹ z` are both `EP`, so `ν` may be evaluated at
  -- either point on the same vector.
  have hν : ∀ x, g (φ'.symm z) = x → ∀ w : TangentSpace IP (g (φ'.symm z)),
      ν.val.tangentHom (g (φ'.symm z), ψ.symm v) w = ν.val.tangentHom (x, ψ.symm v) w := by
    rintro x rfl w
    rfl
  rw [chartTerm_apply, chartTerm_apply, comp_val_tangentHom_apply, hd1, hν _ (congrFun hφ z)]

end InhomogeneousTerm

end TauCeti
