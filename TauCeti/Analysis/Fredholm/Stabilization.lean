/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Analysis.Normed.Operator.Splitting.Family
import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Finite stabilization of Fredholm families

A Fredholm operator becomes surjective after adjoining a finite-dimensional subspace
of its target to its domain. The subspace can be taken inside any dense subspace of the
target, so in Cauchy–Riemann gluing it can be spanned by smooth compactly supported
sections. For a continuous operator family one subspace works throughout a neighbourhood.
A fixed projection onto the stabilized kernel at the base point gives invertible paired
coordinates throughout a smaller neighbourhood.

`ContinuousLinearMap.kernelHomeomorph` then gives product charts on the stabilized
kernel locus with its subspace topology. Their fibre maps are linear, and
`ContinuousLinearMap.contDiffAt_kerSection` gives their inverse parametrizations the
regularity of a smooth operator family. In particular the stabilized kernel dimension
is locally constant, even when the original kernel dimension jumps. These are the
local finite-dimensional kernel models used in determinant line bundles.

Wherever the cokernel keeps its dimension at the base point, the stabilizer remains an exact
topological complement of the range, and the projection onto it along the range varies with the
family; see `ContinuousLinearMap.isTopCompl_of_isInvertible_prod_coprod` and
`ContinuousLinearMap.contDiffAt_snd_comp_kerSection_coprod`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.2 (Fredholm operators and determinant lines).
-/

public section

open Function Set Topology
open Submodule (IsTopCompl)

namespace ContinuousLinearMap

variable {𝕜 E F S : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup S] [NormedSpace 𝕜 S] [FiniteDimensional 𝕜 S]

/-- Adjoining finitely many domain directions preserves Fredholmness. No surjectivity
of the enlarged operator is required. -/
theorem IsFredholm.coprod_of_finiteDimensional {T : E →L[𝕜] F} (hT : IsFredholm T)
    (B : S →L[𝕜] F) : IsFredholm (T.coprod B) := by
  have hker : (fst 𝕜 E S).ker = (⊥ : Submodule 𝕜 E).prod ⊤ := by
    ext p
    simp
  have : FiniteDimensional 𝕜 (fst 𝕜 E S).ker := by
    rw [hker]
    exact (Submodule.prodEquiv (⊥ : Submodule 𝕜 E) (⊤ : Submodule 𝕜 S)).symm.finiteDimensional
  have hf : IsFredholm (fst 𝕜 E S) :=
    isQuotientMap_fst.isFredholm
      (closedComplemented_ker_of_rightInverse (fst 𝕜 E S) (inl 𝕜 E S) (fun _ ↦ rfl))
      inferInstance
  have hB : (B ∘L snd 𝕜 E S).toLinearMap.HasFiniteRange :=
    LinearMap.HasFiniteRange.of_finite_dom.comp_right _
  simpa only [comp_fst_add_comp_snd] using (hT.comp hf).add_hasFiniteRange hB

omit [CompleteSpace 𝕜] in
/-- **Kernel charts of a sum of stabilizers.** A kernel coordinate `q` of the stabilization of
`T` by `D₂` gives the kernel coordinate `(x, (l, l₃)) ↦ (q (x, l), l₃)` of its stabilization by
`D₂.coprod D₃`, for any further directions `D₃`. -/
theorem IsInvertible.prod_coprod_coprod {Λ Λ₃ G : Type*} [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ]
    [NormedAddCommGroup Λ₃] [NormedSpace 𝕜 Λ₃] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G}
    (h : ((T.coprod D₂).prod q).IsInvertible) (D₃ : Λ₃ →L[𝕜] F) :
    ((T.coprod (D₂.coprod D₃)).prod ((q.prodMap (ContinuousLinearMap.id 𝕜 Λ₃)) ∘L
      (ContinuousLinearEquiv.prodAssoc 𝕜 E Λ Λ₃).symm.toContinuousLinearMap)).IsInvertible := by
  obtain ⟨e, he⟩ := h
  have hA (w : F × G) : (T.coprod D₂) (e.symm w) = w.1 := by
    simpa using congrArg Prod.fst (congrArg (· (e.symm w)) he.symm)
  have hq (w : F × G) : q (e.symm w) = w.2 := by
    simpa using congrArg Prod.snd (congrArg (· (e.symm w)) he.symm)
  have he' (z : E × Λ) : e.symm ((T.coprod D₂) z, q z) = z := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact (congrArg (· z) he).symm
  -- The inverse solves `T x + D₂ l = y - D₃ l₃` and `q (x, l) = g` for `(x, l)`.
  let S : F × G × Λ₃ →L[𝕜] (F × G) × Λ₃ :=
    ((fst 𝕜 F (G × Λ₃) - D₃ ∘L snd 𝕜 G Λ₃ ∘L
        snd 𝕜 F (G × Λ₃)).prod
      (fst 𝕜 G Λ₃ ∘L snd 𝕜 F (G × Λ₃))).prod
      (snd 𝕜 G Λ₃ ∘L snd 𝕜 F (G × Λ₃))
  let inv : F × G × Λ₃ →L[𝕜] E × Λ × Λ₃ :=
    (ContinuousLinearEquiv.prodAssoc 𝕜 E Λ Λ₃).toContinuousLinearMap ∘L
      ((e.symm : F × G →L[𝕜] E × Λ).prodMap (ContinuousLinearMap.id 𝕜 Λ₃)) ∘L S
  refine ⟨ContinuousLinearEquiv.equivOfInverse ((T.coprod (D₂.coprod D₃)).prod
    ((q.prodMap (ContinuousLinearMap.id 𝕜 Λ₃)) ∘L
      (ContinuousLinearEquiv.prodAssoc 𝕜 E Λ Λ₃).symm.toContinuousLinearMap)) inv
    (fun z ↦ ?_) (fun w ↦ ?_), rfl⟩
  · obtain ⟨x, l, l₃⟩ := z
    have := he' (x, l)
    simp only [coprod_apply] at this
    simp [inv, S, ← add_assoc, this]
  · obtain ⟨y, g, m⟩ := w
    have h1 := hA (y - D₃ m, g)
    have h2 := hq (y - D₃ m, g)
    simp only [coprod_apply] at h1
    simp [inv, S, ← add_assoc, h1, h2]

omit [CompleteSpace 𝕜] in
/-- **Kernel charts under a change of models.** A kernel coordinate `q` of the stabilization of `T`
by `D₂` stays a kernel coordinate after replacing the stabilizing space `Λ` and the coordinate
space `G` by isomorphic spaces `Λ'` and `G'`: the stabilization by `D₂ ∘ eΛ` paired with
`(x, l) ↦ eG (q (x, eΛ l))` is invertible. -/
theorem IsInvertible.prod_coprod_comp {Λ Λ' G G' : Type*} [NormedAddCommGroup Λ]
    [NormedSpace 𝕜 Λ] [NormedAddCommGroup Λ'] [NormedSpace 𝕜 Λ'] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
    {T : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G}
    (h : ((T.coprod D₂).prod q).IsInvertible) (eΛ : Λ' ≃L[𝕜] Λ) (eG : G ≃L[𝕜] G') :
    ((T.coprod (D₂ ∘L (eΛ : Λ' →L[𝕜] Λ))).prod
      ((eG : G →L[𝕜] G') ∘L q ∘L (ContinuousLinearMap.id 𝕜 E).prodMap (eΛ : Λ' →L[𝕜] Λ))
      ).IsInvertible := by
  have hcomp : (T.coprod (D₂ ∘L (eΛ : Λ' →L[𝕜] Λ))).prod
      ((eG : G →L[𝕜] G') ∘L q ∘L (ContinuousLinearMap.id 𝕜 E).prodMap (eΛ : Λ' →L[𝕜] Λ)) =
      ((ContinuousLinearEquiv.refl 𝕜 F).prodCongr eG : F × G →L[𝕜] F × G') ∘L
        ((T.coprod D₂).prod q) ∘L
        ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr eΛ : E × Λ' →L[𝕜] E × Λ) := by
    ext <;> simp
  rw [hcomp]
  exact (IsInvertible.comp (isInvertible_equiv (f := (ContinuousLinearEquiv.refl 𝕜 F).prodCongr eG))
    h).comp (isInvertible_equiv (f := (ContinuousLinearEquiv.refl 𝕜 E).prodCongr eΛ))

variable [CompleteSpace E] [CompleteSpace F]
  {X : Type*} [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

/-- A family continuous and Fredholm at one point admits a fixed finite-dimensional target
stabilizer and fixed kernel coordinate on a neighbourhood. The stabilizer can be chosen inside any
dense subspace `D` of the target, for instance a space of smooth compactly supported sections, and
it is then a topological complement of the range at the base point. Pairing the stabilized
operator with the coordinate is invertible on the neighbourhood. For continuous families,
`kernelHomeomorph` supplies actual local product charts, with model the finite-dimensional
stabilized kernel at the base point.
No Fredholm hypothesis is imposed away from the base point. At the parameters of the
neighbourhood where the cokernel keeps its dimension at the base point, the stabilizer stays an
exact complement of the range (`ContinuousLinearMap.isTopCompl_of_isInvertible_prod_coprod`). -/
theorem IsFredholm.exists_stabilization_kernel_coordinates (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ IsTopCompl S (T x₀).range ∧ FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
          ∀ x ∈ U, (((T x).coprod S.subtypeL).prod q).IsInvertible := by
  have := hT₀.finite_coker
  obtain ⟨S, hSD, hS⟩ := Submodule.exists_le_isTopCompl_of_dense hT₀.isClosed_range hD
  have : FiniteDimensional 𝕜 S :=
    ((T x₀).range.quotientEquivOfIsCompl S hS.isCompl).finiteDimensional
  have : IsClosed (S : Set F) := S.isClosed_of_finiteDimensional
  let A : X → (E × S) →L[𝕜] F := fun x ↦ (T x).coprod S.subtypeL
  have hsurj : Surjective (A x₀) := by
    apply LinearMap.range_eq_top.mp
    rw [range_coprod, Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact hS.isCompl.sup_eq_top
  have hfred : IsFredholm (A x₀) := hT₀.coprod_of_finiteDimensional S.subtypeL
  let q := Classical.choose hfred.closedComplemented_ker
  have hinv : ((A x₀).prod q).IsInvertible := by
    refine ⟨(A x₀).implicitCoordEquiv (LinearMap.range_eq_top.mpr hsurj)
      hfred.closedComplemented_ker, ?_⟩
    exact coe_implicitCoordEquiv _ _ _
  have hA : ContinuousAt A x₀ := hT.continuousLinearMapCoprod continuousAt_const
  obtain ⟨U, hU, hx₀, hUinv⟩ := exists_isOpen_isInvertible_prod hA hinv
  exact ⟨S, hSD, hS.symm, inferInstance, q, U, hU, hx₀, hUinv⟩

/-- **Kernel charts with standard models.** A Fredholm operator between Banach spaces has a finite
stabilization by `𝕜ⁿ` with a kernel coordinate in `𝕜ᵐ`: some `D₂ : 𝕜ⁿ →L[𝕜] F` and
`q : E × 𝕜ⁿ →L[𝕜] 𝕜ᵐ` make the pair `(T.coprod D₂).prod q` invertible. -/
theorem IsFredholm.exists_isInvertible_prod_coprod {T : E →L[𝕜] F}
    (hT : IsFredholm T) :
    ∃ (n m : ℕ) (D₂ : (Fin n → 𝕜) →L[𝕜] F) (q : E × (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)),
      ((T.coprod D₂).prod q).IsInvertible := by
  obtain ⟨S, -, -, hS, q, U, -, hTU, hU⟩ :=
    hT.exists_stabilization_kernel_coordinates (X := E →L[𝕜] F) (T := fun S ↦ S)
      continuousAt_id (D := ⊤) (by simp)
  have h : ((T.coprod S.subtypeL).prod q).IsInvertible := hU T hTU
  have := (hT.coprod_of_finiteDimensional S.subtypeL).finite_ker
  exact ⟨Module.finrank 𝕜 S, Module.finrank 𝕜 ((T.coprod S.subtypeL).ker), _, _,
    h.prod_coprod_comp (.ofFinrankEq (by simp)) (.ofFinrankEq (by simp))⟩

end ContinuousLinearMap
