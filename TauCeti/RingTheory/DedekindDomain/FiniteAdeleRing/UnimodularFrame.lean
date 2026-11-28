/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Pi
import TauCeti.LinearAlgebra.Matrix.SubalgebraEntries
import TauCeti.LinearAlgebra.Matrix.Submatrix

/-!
# Unimodular frames over the integral finite adeles

Let `R` be a Dedekind domain with fraction field `K` and `Ô = ∏_v 𝒪_v` the integral finite adeles.
A *primitive* `ν × β` matrix over the finite adeles is one with entries in `Ô` and a left inverse
with entries in `Ô`. Every primitive matrix is the block of the first columns of an element of
`GL_ν(Ô)`, viewed in `GL_ν(𝔸_f)` through `IsDedekindDomain.FiniteAdeleRing.integralGL`: the ring
`Ô` is isomorphic to the product of the local rings `𝒪_v`
(`IsDedekindDomain.FiniteAdeleRing.isEmbedding_integralEmbedding`,
`IsDedekindDomain.FiniteAdeleRing.range_integralEmbedding`), and over a product of local rings
every unimodular frame completes to an invertible matrix
(`TauCeti.exists_smul_eq_of_mul_eq_one_pi`). The ring `Ô` itself is not semilocal, so
`TauCeti.exists_smul_eq_of_mul_eq_one` does not apply to it directly.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.exists_submatrix_eq_of_mul_eq_one`: a primitive matrix is the
  block of the columns `f (β)` of an element of `GL_ν(Ô)`, for any injective `f : β → ν`.
-/

public section
noncomputable section

open Matrix

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {ν β : Type*} [Fintype ν] [DecidableEq ν] [DecidableEq β]

/-- The product of the local rings of integers is isomorphic to `Ô` through `integralEmbedding`,
which is injective with image `Ô`. -/
private def integralEquiv :
    (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) ≃+* integralAdeles R K :=
  RingEquiv.ofBijective (RingHom.codRestrict
      (integralEmbedding (R := R) (K := K) :
        (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) →+* FiniteAdeleRing R K)
      (integralAdeles R K) fun x ↦ by
        rw [← SetLike.mem_coe, ← range_integralEmbedding]
        exact ⟨x, rfl⟩)
    ⟨fun _ _ hxy ↦ (isEmbedding_integralEmbedding (R := R) (K := K)).injective
        (congrArg Subtype.val hxy),
      fun y ↦ by
        have hy : (y : FiniteAdeleRing R K) ∈ Set.range (integralEmbedding (R := R) (K := K)) := by
          rw [range_integralEmbedding]
          exact y.property
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, Subtype.ext hx⟩⟩

/-- Over the integral finite adeles `Ô`, every primitive matrix is the block of columns of an
invertible matrix: if `n` and `l` have integral entries and `l * n = 1`, then for every injective
`f : β → ν` there is `g ∈ GL_ν(Ô)` whose columns `f (β)`, in `GL_ν(𝔸_f)`, are those of `n`. -/
theorem exists_submatrix_eq_of_mul_eq_one {f : β → ν} (hf : Function.Injective f)
    {n : Matrix ν β (FiniteAdeleRing R K)} {l : Matrix β ν (FiniteAdeleRing R K)}
    (hn : ∀ i j, n i j ∈ integralAdeles R K) (hl : ∀ i j, l i j ∈ integralAdeles R K)
    (h : l * n = 1) :
    ∃ g : GL ν (integralAdeles R K),
      (integralGL K ν g : Matrix ν ν (FiniteAdeleRing R K)).submatrix id f = n := by
  have : Finite β := Finite.of_injective f hf
  set ψ := integralEquiv (R := R) (K := K)
  -- Lift `n` and `l` to `Ô`, and then to the product of the local rings of integers.
  obtain ⟨n', rfl⟩ := Subalgebra.exists_map_algebraMap_eq hn
  obtain ⟨l', rfl⟩ := Subalgebra.exists_map_algebraMap_eq hl
  have h₀ : l' * n' = 1 := by
    refine Matrix.map_injective (f := algebraMap (integralAdeles R K) (FiniteAdeleRing R K))
      Subtype.val_injective ?_
    dsimp only
    rw [Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h' : l'.map ψ.symm * n'.map ψ.symm = 1 := by
    rw [← Matrix.map_mul, h₀, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨g, hg⟩ := TauCeti.exists_smul_eq_of_mul_eq_one_pi
    (submatrix_one_mul_submatrix_one ⟨f, hf⟩) h'
  have hgf : (g : Matrix ν ν _).submatrix id f = n'.map ψ.symm := by
    rw [← hg, GeneralLinearGroup.smul_def, mul_submatrix_id, Matrix.mul_one,
      Function.Embedding.coeFn_mk]
  -- Push the invertible matrix into `GL_ν(Ô)` along the isomorphism.
  refine ⟨GeneralLinearGroup.map ψ.toRingHom g, Matrix.ext fun i j ↦ ?_⟩
  have hij := congrArg ψ (congrFun₂ hgf i j)
  rw [submatrix_apply, map_apply, RingEquiv.apply_symm_apply] at hij
  rw [submatrix_apply, integralGL_apply, map_apply, ← hij, id_eq,
    GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    Subalgebra.algebraMap_apply]

end IsDedekindDomain.FiniteAdeleRing
