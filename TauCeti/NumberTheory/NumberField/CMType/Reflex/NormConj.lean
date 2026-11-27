/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Norm
import TauCeti.RingTheory.Unramified.TraceRepresentation

/-!
# The reflex norm of the complementary type

Let `Φ` be a CM type on a number field `E` and `σ` a ring automorphism of `E` with
`φ ∘ σ = ι ∘ φ` for every complex embedding `φ`, such as complex conjugation `ι_E` of a CM field.
For a subfield `k ⊆ ℂ` containing the reflex field, the reflex norm of the complementary type
`ιΦ` is `N_{k,ιΦ} = σ⁻¹ ∘ N_{k,Φ}` (`TauCeti.CMType.reflexNorm_star_apply`); for a CM field,
`N_{k,ιΦ} = ι_E ∘ N_{k,Φ}` (`TauCeti.CMType.reflexNorm_star_apply_complexConj`), as in Milne,
*Complex Multiplication*, Remark 1.24(b), p.16.

Twisting the action of `E` on the representation `V` with the type trace of `Φ` by `σ` gives a
representation with the type trace of `ιΦ`, since `typeTrace_Φ(σ c) = typeTrace_{ιΦ}(c)`. So the
representation `V'` of `ιΦ` is `σ`-semilinearly isomorphic to `V`, compatibly with `k`, and the
determinant over `E` of the scalar action of `k` changes by `σ⁻¹`
(`TauCeti.smulDet_eq_symm_apply_of_map_smul`).

## Main results

* `TauCeti.smulDet_eq_symm_apply_of_map_smul`: a `σ`-semilinear `k`-linear isomorphism changes the
  determinant of the scalar action by `σ⁻¹`.
* `TauCeti.CMType.reflexNorm_star_apply`: `N_{k,ιΦ}(a) = σ⁻¹(N_{k,Φ}(a))`.
* `TauCeti.CMType.reflexNorm_star_apply_complexConj`: on a CM field, `N_{k,ιΦ} = ι_E ∘ N_{k,Φ}`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Remark 1.24(b), p.16.
-/

public section

namespace TauCeti

section Twist

variable {E k V V' : Type*} [CommRing E] [Semiring k] [AddCommGroup V] [Module E V] [Module k V]
  [SMulCommClass E k V] [AddCommGroup V'] [Module E V'] [Module k V'] [SMulCommClass E k V']

/-- The basis of `V'` corresponding to a basis of `V` under a `σ`-semilinear isomorphism
`e : V' ≃ V`: the coordinates of `v` are `σ⁻¹` of those of `e v`. -/
private noncomputable def twistBasis (σ : E ≃+* E) (e : V' ≃+ V)
    (he : ∀ (c : E) (v : V'), e (c • v) = σ c • e v) {ι : Type*} (b : Module.Basis ι E V) :
    Module.Basis ι E V' :=
  .ofRepr
    { toFun v := (b.repr (e v)).mapRange σ.symm (map_zero _)
      invFun x := e.symm (b.repr.symm (x.mapRange σ (map_zero _)))
      map_add' v w := by
        rw [map_add, map_add]
        exact Finsupp.mapRange_add (map_add σ.symm) _ _
      map_smul' c v := by
        ext i
        simp [he]
      left_inv v := by
        have h : ((b.repr (e v)).mapRange σ.symm (map_zero _)).mapRange σ (map_zero _) =
            b.repr (e v) := by
          ext
          simp
        simp only [h, LinearEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      right_inv x := by
        ext i
        simp }

private theorem twistBasis_repr (σ : E ≃+* E) (e : V' ≃+ V)
    (he : ∀ (c : E) (v : V'), e (c • v) = σ c • e v) {ι : Type*} (b : Module.Basis ι E V)
    (v : V') (i : ι) : (twistBasis σ e he b).repr v i = σ.symm (b.repr (e v) i) :=
  rfl

private theorem twistBasis_apply (σ : E ≃+* E) (e : V' ≃+ V)
    (he : ∀ (c : E) (v : V'), e (c • v) = σ c • e v) {ι : Type*} (b : Module.Basis ι E V)
    (i : ι) : e (twistBasis σ e he b i) = b i := by
  classical
  rw [← e.apply_symm_apply (b i)]
  congr 1
  apply (twistBasis σ e he b).repr.injective
  ext j
  rw [Module.Basis.repr_self, twistBasis_repr, AddEquiv.apply_symm_apply, Module.Basis.repr_self]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp

/-- The determinant is the junk value `1` on a module without a finite basis. -/
private theorem det_eq_one_of_not_exists_basis {M : Type*} [AddCommGroup M] [Module E M]
    (H : ¬∃ s : Finset M, Nonempty (Module.Basis s E M)) (f : M →ₗ[E] M) : f.det = 1 := by
  classical
  simp [LinearMap.det_def, H]

/-- **A semilinear twist changes the determinant of the scalar action by `σ⁻¹`.** If a
`k`-linear isomorphism `e : V' ≃ V` satisfies `e (c • v) = σ c • e v` for a ring automorphism
`σ` of `E`, then `det_E(a | V') = σ⁻¹(det_E(a | V))` for every `a ∈ k`. -/
theorem smulDet_eq_symm_apply_of_map_smul (σ : E ≃+* E) (e : V' ≃ₗ[k] V)
    (he : ∀ (c : E) (v : V'), e (c • v) = σ c • e v) (a : k) :
    smulDet E k V' a = σ.symm (smulDet E k V a) := by
  have : SMulCommClass k E V := .symm E k V
  have : SMulCommClass k E V' := .symm E k V'
  have he' (c : E) (v : V) : e.symm (c • v) = σ.symm c • e.symm v := by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [smulDet_apply, smulDet_apply]
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s E V)
  · classical
    obtain ⟨s, ⟨b⟩⟩ := H
    let b' := twistBasis σ e.toAddEquiv he b
    rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b', RingEquiv.map_det]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    change _ = σ.symm (LinearMap.toMatrix b b _ i j)
    rw [LinearMap.toMatrix_apply, twistBasis_repr]
    congr 2
    rw [DistribSMul.toLinearMap_apply, DistribSMul.toLinearMap_apply]
    change b.repr (e (a • b' j)) = _
    rw [e.map_smul]
    exact congrArg (fun x ↦ b.repr (a • x)) (twistBasis_apply σ e.toAddEquiv he b j)
  · have H' : ¬∃ s : Finset V', Nonempty (Module.Basis s E V') := fun ⟨s, ⟨b⟩⟩ ↦ by
      classical
      exact H ⟨_, ⟨(twistBasis σ.symm e.symm.toAddEquiv he' b).reindexFinsetRange⟩⟩
    rw [det_eq_one_of_not_exists_basis H, det_eq_one_of_not_exists_basis H', map_one]

end Twist

namespace CMType

variable {E : Type*} [Field E] [NumberField E] {k : IntermediateField ℚ ℂ}

-- A number field is formally unramified over `ℚ`, so its reflex norm is defined.
attribute [local instance] Algebra.FormallyUnramified.of_isSeparable

/-- **The reflex norm of the complementary type.** If a ring automorphism `σ` of `E` satisfies
`φ ∘ σ = ι ∘ φ` for every complex embedding `φ`, then `N_{k,ιΦ}(a) = σ⁻¹(N_{k,Φ}(a))`. -/
theorem reflexNorm_star_apply (Φ : CMType E) (hk : Φ.reflexField ≤ k) (σ : E ≃+* E)
    (hσ : ∀ φ : E →+* ℂ, φ.comp σ.toRingHom = star φ) (a : k) :
    (star Φ).reflexNorm (reflexField_star Φ ▸ hk) a = σ.symm (Φ.reflexNorm hk a) := by
  -- The representations `V` and `V'` with the type traces of `Φ` and `ιΦ`.
  obtain ⟨n, ρ, hρ⟩ := Φ.exists_trace_eq_typeTrace hk
  obtain ⟨n', ρ', hρ'⟩ := (star Φ).exists_trace_eq_typeTrace (reflexField_star Φ ▸ hk)
  let V := Fin n → k
  let V' := Fin n' → k
  let := Module.compHom V ρ
  have := SMul.comp.smulCommClass (α := V) (β := k) ρ
  let := Module.compHom V' ρ'
  have := SMul.comp.smulCommClass (α := V') (β := k) ρ'
  have hV (c : E) : (LinearMap.trace k V (DistribSMul.toLinearMap k V c) : ℂ) = Φ.typeTrace c := by
    rw [DistribSMul.toLinearMap_compHom]
    exact hρ c
  have hV' (c : E) : (LinearMap.trace k V' (DistribSMul.toLinearMap k V' c) : ℂ) =
      (star Φ).typeTrace c := by
    rw [DistribSMul.toLinearMap_compHom]
    exact hρ' c
  -- Twisted by `σ`, `V` has the type trace of `ιΦ`: `typeTrace_Φ(σ c) = typeTrace_{ιΦ}(c)`.
  have htw (c : E) : LinearMap.trace k V' (ρ' c) = LinearMap.trace k V (ρ (σ c)) := by
    refine Subtype.ext ((hρ' c).trans ?_)
    rw [hρ, typeTrace_apply, typeTrace_apply, coe_star_eq_image,
      finsum_mem_image star_injective.injOn]
    exact finsum_congr fun φ ↦ finsum_congr fun _ ↦ (RingHom.congr_fun (hσ φ) c).symm
  obtain ⟨e, he⟩ := exists_linearEquiv_of_trace_eq (R := ℚ) ρ'.toRatAlgHom
    (ρ.comp σ.toRingHom).toRatAlgHom fun c ↦ by
      rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply]
      exact htw c
  rw [reflexNorm_eq_smulDet Φ hk V hV, reflexNorm_eq_smulDet (star Φ) _ V' hV']
  refine smulDet_eq_symm_apply_of_map_smul σ e (fun c v ↦ ?_) a
  have := he c v
  rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply] at this
  exact this

/-- **The reflex norm of the complementary type of a CM field** is the complex conjugate of the
reflex norm: `N_{k,ιΦ} = ι_E ∘ N_{k,Φ}`. -/
theorem reflexNorm_star_apply_complexConj [NumberField.IsCMField E] (Φ : CMType E)
    (hk : Φ.reflexField ≤ k) (a : k) :
    (star Φ).reflexNorm (reflexField_star Φ ▸ hk) a =
      NumberField.IsCMField.complexConj E (Φ.reflexNorm hk a) := by
  rw [reflexNorm_star_apply Φ hk (NumberField.IsCMField.complexConj E).toRingEquiv
    fun φ ↦ RingHom.ext fun x ↦ by simp [RingHom.star_apply]]
  apply (NumberField.IsCMField.complexConj E).injective
  simp

end CMType

end TauCeti
