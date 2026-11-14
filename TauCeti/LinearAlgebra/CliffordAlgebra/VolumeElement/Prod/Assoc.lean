/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Orientation.WithLp
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Associativity of graded tensor products of complex Clifford modules

Let `(U, o₁)` and `(V, o₂)` be even-dimensional oriented real inner product spaces of dimensions
`k` and `n` with `Q₁ u = -‖u‖²` and `Q₂ v = -‖v‖²`, and let `(W, Q₃)` be an arbitrary real inner
product space. Orient `U ⊕ V` (`WithLp 2 (U × V)`) by the product orientation `o₁₂` transported
from `Orientation.prod o₁ o₂`.

On `(E ⊗ F) ⊗ G`, the chirality of `(U ⊕ V, o₁₂)` acts on `E ⊗ F` by `Γ_U ⊗ Γ_V`
(`CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod`), so a real vector `((u, v), w)` of
`(U ⊕ V) ⊕ W` acts by

  `(c_U(u) ⊗ 1 + Γ_U ⊗ c_V(v)) ⊗ 1 + (Γ_U ⊗ Γ_V) ⊗ c_W(w)`.

Under Mathlib's `TensorProduct.assoc ℂ E F G`, this matches the right-associated action

  `c_U(u) ⊗ (1 ⊗ 1) + Γ_U ⊗ (c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w))`

of `(u, (v, w))` on `E ⊗ (F ⊗ G)`, so `TensorProduct.assoc ℂ E F G` intertwines the two iterated
`complexProdTensor` actions on all of `CliffordAlgebra (Q_L.baseChange ℂ)` along
`QuadraticMap.IsometryEquiv.withLpProdAssoc`. No finiteness or negative-definiteness assumption on
`(W, Q₃)` is needed for the Clifford intertwining; when `(W, o₃)` is also even-dimensional with
`Q₃ w = -‖w‖²`, `Orientation.map_withLpProdAssoc_prod` identifies the two iterated product
orientations and `TensorProduct.assoc ℂ E F G` carries the left-associated product chirality to the
right-associated one.

## Main results

* `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
  `CliffordAlgebra.assoc_complexProdTensor`: `TensorProduct.assoc ℂ E F G` intertwines the two
  iterated `complexProdTensor` actions along `QuadraticMap.IsometryEquiv.withLpProdAssoc`.
* `CliffordAlgebra.assoc_complexProdTensor_complexVolume`: for even-dimensional `(W, o₃)` with
  `Q₃ w = -‖w‖²`, `TensorProduct.assoc ℂ E F G` carries the left-associated chirality action to the
  right-associated one when `o_R` is transported from `o_L` along `LinearEquiv.withLpProdAssoc`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))} {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q_L : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q_R : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ U] {k : ℕ} [Fact (finrank ℝ U = k)] (o₁ : Orientation ℝ U (Fin k))
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₂ : Orientation ℝ V (Fin n))
  [Fact (finrank ℝ (WithLp 2 (U × V)) = k + n)]
  (o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (k + n)))
  (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hk : Even k)
  (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2) (hn : Even n)
  (hQ₁₂_norm : ∀ x, Q₁₂ x = -‖x‖ ^ 2) (hkn : Even (k + n))
  {E F G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

/-- **Associativity of `complexProdTensor` (algebra-map form).** Conjugating the left-associated
action on `(E ⊗ F) ⊗ G` by `TensorProduct.assoc ℂ E F G` gives the right-associated action on
`E ⊗ (F ⊗ G)` transported along `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
theorem conjAlgEquiv_assoc_complexProdTensor
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
          hQ_R).toIsometry.baseChange ℂ)) := by
  have hvol := complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn hQ₂ ho₁₂
  refine AlgHom.toRingHom_injective <| baseChange_ringHom_ext Q_L (fun _ ↦ by simp) fun x ↦ ?_
  obtain ⟨⟨uv, w⟩, rfl⟩ : ∃ p : WithLp 2 (U × V) × W, WithLp.toLp 2 p = x :=
    ⟨WithLp.ofLp x, by simp⟩
  obtain ⟨⟨u, v⟩, rfl⟩ : ∃ q : U × V, WithLp.toLp 2 q = uv :=
    ⟨WithLp.ofLp uv, by simp⟩
  apply TensorProduct.ext_threefold'
  intro e f g
  simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, hvol,
    QuadraticMap.Isometry.baseChange_tmul, TensorProduct.tmul_add, add_assoc]

/-- **Associativity of `complexProdTensor` (pointwise form).** `TensorProduct.assoc ℂ E F G`
intertwines the two iterated `complexProdTensor` actions for every Clifford element `a` and tensor
`t : (E ⊗ F) ⊗ G`. -/
theorem assoc_complexProdTensor
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q_L.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    (TensorProduct.assoc ℂ E F G)
        (complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)
        (map ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
          hQ_R).toIsometry.baseChange ℂ) a)
        ((TensorProduct.assoc ℂ E F G) t) := by
  have h := congrArg (fun φ : CliffordAlgebra (Q_L.baseChange ℂ) →ₐ[ℂ]
        Module.End ℂ (E ⊗[ℂ] (F ⊗[ℂ] G)) ↦ φ a ((TensorProduct.assoc ℂ E F G) t))
    (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ_L hQ_R o₁ o₂ o₁₂ hQ₁ hk hQ₂ hn
      hQ₁₂_norm hkn ρ₁ ρ₂ ρ₃ ho₁₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- **Associativity on the product chirality.** When `(W, o₃)` is also even-dimensional with
`Q₃ w = -‖w‖²` and `o_R` is obtained from the left-associated product orientation `o_L` along
`LinearEquiv.withLpProdAssoc`, `TensorProduct.assoc ℂ E F G` carries the left-associated chirality
action `(Γ_U ⊗ Γ_V) ⊗ Γ_W` to `Γ_U ⊗ (Γ_V ⊗ Γ_W)`. -/
theorem assoc_complexProdTensor_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₃ : Orientation ℝ W (Fin m))
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    (o₂₃ : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = k + n + m)]
    (o_L : Orientation ℝ (WithLp 2 (WithLp 2 (U × V) × W)) (Fin (k + n + m)))
    [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = k + (n + m))]
    (o_R : Orientation ℝ (WithLp 2 (U × WithLp 2 (V × W))) (Fin (k + (n + m))))
    (hQ₃ : ∀ w, Q₃ w = -‖w‖ ^ 2) (hm : Even m)
    (hQ₂₃_norm : ∀ y, Q₂₃ y = -‖y‖ ^ 2) (hnm : Even (n + m))
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (ho₂₃ : (o₂.prod o₃ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o₂₃)
    (ho_L : (o₁₂.prod o₃ Fact.out Fact.out).map (Fin (k + n + m))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm = o_L)
    (ho_R : Orientation.reindex ℝ (WithLp 2 (U × WithLp 2 (V × W))) (finCongr (add_assoc k n m))
      (o_L.map (Fin (k + n + m)) (LinearEquiv.withLpProdAssoc 2 ℝ U V W)) = o_R)
    (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    (TensorProduct.assoc ℂ E F G)
        (complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ (complexVolume Q_L o_L) t) =
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) (complexVolume Q_R o_R)
        ((TensorProduct.assoc ℂ E F G) t) := by
  have ho_R' : (o₁.prod o₂₃ Fact.out Fact.out).map (Fin (k + (n + m)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm = o_R := by
    rw [← ho_R, ← ho_L]
    have hassoc := Orientation.map_withLpProdAssoc_prod (p := 2) o₁ o₂ o₃
      (Fact.out : finrank ℝ U = k) (Fact.out : finrank ℝ V = n) (Fact.out : finrank ℝ W = m)
    simp only [ho₁₂, ho₂₃] at hassoc
    rw [hassoc, Orientation.reindex_finCongr_reindex_finCongr, finCongr_refl,
      Orientation.reindex_refl, Equiv.refl_apply]
  rw [complexProdTensor_complexVolume_of_map_prod hQ_L o₁₂ hQ₁₂_norm hkn _ ρ₃ o₃ o_L hm hQ₃ ho_L,
    complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn hQ₂ ho₁₂,
    complexProdTensor_complexVolume_of_map_prod hQ_R o₁ hQ₁ hk ρ₁ _ o₂₃ o_R hnm hQ₂₃_norm ho_R',
    complexProdTensor_complexVolume_of_map_prod hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃ o₃ o₂₃ hm hQ₃ ho₂₃]
  exact (TensorProduct.map_map_assoc _ _ _ t).symm

end CliffordAlgebra
