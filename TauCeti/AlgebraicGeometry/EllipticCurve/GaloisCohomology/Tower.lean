/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EmbeddingIndependence

/-!
# Restriction in towers, and restriction of Selmer groups

Let `W` be a Weierstrass curve over a field `K` and `K → L → M` a tower of field extensions.
Restriction of the Galois cohomology of `W` is transitive: restricting from `K` to `L` and then
from `L` to `M` is restricting from `K` to `M`,

```text
H¹(G_K, E(Kˢ)) → H¹(G_L, E(Lˢ)) → H¹(G_M, E(Mˢ))   =   H¹(G_K, E(Kˢ)) → H¹(G_M, E(Mˢ)),
```

up to the identification of the coefficients of `(W⁄L)⁄M` with those of `W⁄M`
(`WeierstrassCurve.pointRes_pointRes`, `WeierstrassCurve.torsionRes_torsionRes`). Since
restriction does not depend on the embeddings of separable closures, any embedding `Kˢ → Mˢ` may
be used on the right.

The main consequence is that restriction to an extension `L/K` carries the Shafarevich–Tate and
Selmer groups of `W` into those of `W⁄L`
(`WeierstrassCurve.pointRes_mem_shafarevichTateGroup`,
`WeierstrassCurve.torsionRes_mem_selmerGroup`). Here the local fields `L' j` defining the groups
over `L` must each lie over one of the local fields `K' (σ j)` defining the groups over `K`, as the
completion `L_w` of a number field lies over the completion `K_v` at the place `v` below `w`: a
class vanishing over `K_v` vanishes over `L_w`, and the two towers `K → L → L_w` and
`K → K_v → L_w` give the same restriction to `L_w`. For `L = K(E[m])` this reduces the
finiteness of `Sel_m(E/K)` to the finiteness of `Sel_m(E/L)` together with the finiteness of the
kernel of restriction to `L` (Silverman, the proof of X.4.2).

## Main results

* `WeierstrassCurve.pointRes_pointRes`, `WeierstrassCurve.torsionRes_torsionRes`: restriction is
  transitive in towers.
* `WeierstrassCurve.pointRes_pointRes_eq_zero_iff`,
  `WeierstrassCurve.torsionRes_torsionRes_eq_zero_iff`: a class restricts to zero along a tower
  exactly when it restricts to zero directly.
* `WeierstrassCurve.pointRes_mem_shafarevichTateGroup`: restriction maps `Sha(E/K)` into
  `Sha(E/L)`.
* `WeierstrassCurve.torsionRes_mem_selmerGroup`: restriction maps `Sel_m(E/K)` into `Sel_m(E/L)`.
* `WeierstrassCurve.finite_selmerGroup_of_finite_ker_torsionRes`: `Sel_m(E/K)` is finite if
  `Sel_m(E/L)` is and restriction to `L` has finite kernel.

## Implementation notes

The identification of `(W⁄L)⁄M` with `W⁄M` is Mathlib's `WeierstrassCurve.map_baseChange` at
`IsScalarTower.toAlgHom K L M`, restated by `show` in terms of base change, as in
`WeierstrassCurve.pointCoeffBaseChange_pointCoeffBaseChange`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (W : WeierstrassCurve K)
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-! ### Restriction in a tower -/

section Tower

variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  (τ' : SeparableClosure L →ₐ[L] SeparableClosure M)
  (τ'' : SeparableClosure K →ₐ[K] SeparableClosure M)

/-- **Restriction on `H¹(G_K, E(Kˢ))` is transitive** in a tower `K → L → M`: restricting to `L`
along `τ` and then to `M` along `τ'` is restricting to `M` along any embedding `τ'' : Kˢ → Mˢ`,
followed by the identification of `(W⁄L)⁄M` with `W⁄M`. -/
theorem pointRes_pointRes (c : H1 (AbsoluteGaloisGroup K) W.PointCoeff) :
    (W⁄L).pointRes τ' (W.pointRes τ c) =
      explicitCoeff1Equiv _ _
        (AddEquiv.cast (M := PointCoeff) (show (W⁄L)⁄M = W⁄M from
          W.map_baseChange (IsScalarTower.toAlgHom K L M)).symm)
        continuous_of_discreteTopology continuous_of_discreteTopology (cast_pointCoeff_smul _)
        (W.pointRes τ'' c) := by
  rw [W.pointRes_eq_pointRes τ'' (compSeparableClosure τ τ'), pointRes_eq_explicitMap1,
    pointRes_eq_explicitMap1, pointRes_eq_explicitMap1]
  simp only [explicitCoeff1Equiv_apply]
  -- The coefficient map is the pullback along the identity and the coefficient equivalence.
  refine Eq.trans ?_ (DFunLike.congr_fun (explicitCoeff1_eq_explicitMap1 _ _ _ _) _).symm
  exact explicitMap1_explicitMap1_of_comp_eq (φ := absoluteGaloisGroupMap τ)
    (f := W.pointCoeffBaseChange τ) (ψ := absoluteGaloisGroupMap τ')
    (q := (W⁄L).pointCoeffBaseChange τ') (φ' := absoluteGaloisGroupMap (compSeparableClosure τ τ'))
    (f' := W.pointCoeffBaseChange (compSeparableClosure τ τ')) (ψ' := ContinuousMonoidHom.id _)
    (q' := (AddEquiv.cast (M := PointCoeff) (show (W⁄L)⁄M = W⁄M from
      W.map_baseChange (IsScalarTower.toAlgHom K L M)).symm).toAddMonoidHom)
    (hf := continuous_of_discreteTopology) (hequiv := W.pointCoeffBaseChange_smul τ)
    (hq := continuous_of_discreteTopology) (hequivq := (W⁄L).pointCoeffBaseChange_smul τ')
    (hf' := continuous_of_discreteTopology)
    (hequiv' := W.pointCoeffBaseChange_smul (compSeparableClosure τ τ'))
    (hq' := continuous_of_discreteTopology) (hequivq' := cast_pointCoeff_smul _)
    (hφ := ContinuousMonoidHom.ext fun g ↦
      (absoluteGaloisGroupMap_compSeparableClosure τ τ' g).symm)
    (hqf := AddMonoidHom.ext fun P ↦
      W.pointCoeffBaseChange_pointCoeffBaseChange τ τ' _ (compSeparableClosure_apply τ τ') P)
    (x := c)

/-- **Restriction on `H¹(G_K, E(Kˢ)[m])` is transitive** in a tower `K → L → M`, as in
`WeierstrassCurve.pointRes_pointRes`. -/
theorem torsionRes_torsionRes (m : ℕ) (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    (W⁄L).torsionRes τ' m (W.torsionRes τ m c) =
      explicitCoeff1Equiv _ _
        (AddEquiv.cast (M := fun V : WeierstrassCurve M ↦ V.TorsionCoeff m)
          (show (W⁄L)⁄M = W⁄M from
            W.map_baseChange (IsScalarTower.toAlgHom K L M)).symm)
        continuous_of_discreteTopology continuous_of_discreteTopology (cast_torsionCoeff_smul _)
        (W.torsionRes τ'' m c) := by
  rw [W.torsionRes_eq_torsionRes τ'' (compSeparableClosure τ τ'), torsionRes_eq_explicitMap1,
    torsionRes_eq_explicitMap1, torsionRes_eq_explicitMap1]
  simp only [explicitCoeff1Equiv_apply]
  -- The coefficient map is the pullback along the identity and the coefficient equivalence.
  refine Eq.trans ?_ (DFunLike.congr_fun (explicitCoeff1_eq_explicitMap1 _ _ _ _) _).symm
  exact explicitMap1_explicitMap1_of_comp_eq (φ := absoluteGaloisGroupMap τ)
    (f := W.torsionCoeffBaseChange τ m) (ψ := absoluteGaloisGroupMap τ')
    (q := (W⁄L).torsionCoeffBaseChange τ' m)
    (φ' := absoluteGaloisGroupMap (compSeparableClosure τ τ'))
    (f' := W.torsionCoeffBaseChange (compSeparableClosure τ τ') m)
    (ψ' := ContinuousMonoidHom.id _)
    (q' := (AddEquiv.cast (M := fun V : WeierstrassCurve M ↦ V.TorsionCoeff m)
      (show (W⁄L)⁄M = W⁄M from
        W.map_baseChange (IsScalarTower.toAlgHom K L M)).symm).toAddMonoidHom)
    (hf := continuous_of_discreteTopology) (hequiv := W.torsionCoeffBaseChange_smul τ m)
    (hq := continuous_of_discreteTopology) (hequivq := (W⁄L).torsionCoeffBaseChange_smul τ' m)
    (hf' := continuous_of_discreteTopology)
    (hequiv' := W.torsionCoeffBaseChange_smul (compSeparableClosure τ τ') m)
    (hq' := continuous_of_discreteTopology) (hequivq' := cast_torsionCoeff_smul _)
    (hφ := ContinuousMonoidHom.ext fun g ↦
      (absoluteGaloisGroupMap_compSeparableClosure τ τ' g).symm)
    (hqf := AddMonoidHom.ext fun P ↦
      W.torsionCoeffBaseChange_torsionCoeffBaseChange τ τ' _ (compSeparableClosure_apply τ τ') m P)
    (x := c)

/-- A class of `H¹(G_K, E(Kˢ))` restricts to zero along the tower `K → L → M` exactly when it
restricts to zero along any embedding `Kˢ → Mˢ`. -/
theorem pointRes_pointRes_eq_zero_iff {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff} :
    (W⁄L).pointRes τ' (W.pointRes τ c) = 0 ↔ W.pointRes τ'' c = 0 := by
  rw [W.pointRes_pointRes τ τ' τ'', AddEquivClass.map_eq_zero_iff]

/-- A class of `H¹(G_K, E(Kˢ)[m])` restricts to zero along the tower `K → L → M` exactly when it
restricts to zero along any embedding `Kˢ → Mˢ`. -/
theorem torsionRes_torsionRes_eq_zero_iff {m : ℕ}
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    (W⁄L).torsionRes τ' m (W.torsionRes τ m c) = 0 ↔ W.torsionRes τ'' m c = 0 := by
  rw [W.torsionRes_torsionRes τ τ' τ'', AddEquivClass.map_eq_zero_iff]

end Tower

/-! ### Restriction of the Shafarevich–Tate and Selmer groups -/

section Selmer

variable {ι : Type*} {K' : ι → Type*} [∀ i, Field (K' i)] [∀ i, Algebra K (K' i)]
  (τK : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (K' i))
  {J : Type*} {L' : J → Type*} [∀ j, Field (L' j)] [∀ j, Algebra L (L' j)]
  (τL : ∀ j, SeparableClosure L →ₐ[L] SeparableClosure (L' j))
  (σ : J → ι) [∀ j, Algebra K (L' j)] [∀ j, IsScalarTower K L (L' j)]
  [∀ j, Algebra (K' (σ j)) (L' j)] [∀ j, IsScalarTower K (K' (σ j)) (L' j)]

include σ in
/-- **Restriction maps `Sha(E/K)` into `Sha(E/L)`.** If each field `L' j` defining the
Shafarevich–Tate group of `W⁄L` is an extension of the field `K' (σ j)` defining that of `W`,
compatibly with `K → L → L' j`, then restriction to `L` carries the Shafarevich–Tate group of `W`
into that of `W⁄L`: a class vanishing over `K' (σ j)` vanishes over `L' j`. -/
theorem pointRes_mem_shafarevichTateGroup {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff}
    (hc : c ∈ W.shafarevichTateGroup τK) :
    W.pointRes τ c ∈ (W⁄L).shafarevichTateGroup τL := by
  rw [mem_shafarevichTateGroup_iff] at hc ⊢
  intro j
  let ρ : SeparableClosure (K' (σ j)) →ₐ[K' (σ j)] SeparableClosure (L' j) := IsSepClosed.lift
  let τ'' : SeparableClosure K →ₐ[K] SeparableClosure (L' j) := IsSepClosed.lift
  -- Both towers `K → L → L' j` and `K → K' (σ j) → L' j` restrict to `L' j` along `τ''`.
  rw [W.pointRes_pointRes_eq_zero_iff τ (τL j) τ'',
    ← W.pointRes_pointRes_eq_zero_iff (τK (σ j)) ρ τ'', hc, map_zero]

include σ in
/-- **Restriction maps `Sel_m(E/K)` into `Sel_m(E/L)`**, under the compatibility of the defining
fields of `WeierstrassCurve.pointRes_mem_shafarevichTateGroup`. -/
theorem torsionRes_mem_selmerGroup {m : ℕ} {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (hc : c ∈ W.selmerGroup τK m) :
    W.torsionRes τ m c ∈ (W⁄L).selmerGroup τL m := by
  rw [mem_selmerGroup_iff] at hc ⊢
  rw [← pointRes_torsionCoeffIncl]
  exact W.pointRes_mem_shafarevichTateGroup τ τK τL σ hc

include σ in
/-- **Finiteness of `Sel_m(E/L)` gives finiteness of `Sel_m(E/K)`** when restriction of
`H¹(G_K, E(Kˢ)[m])` to `L` has finite kernel, under the compatibility of the defining fields of
`WeierstrassCurve.pointRes_mem_shafarevichTateGroup`: restriction maps `Sel_m(E/K)` into the
finite group `Sel_m(E/L)` with finite kernel. -/
theorem finite_selmerGroup_of_finite_ker_torsionRes {m : ℕ} (hker : Finite (W.torsionRes τ m).ker)
    (hL : Finite ((W⁄L).selmerGroup τL m)) : Finite (W.selmerGroup τK m) := by
  let f := (W.torsionRes τ m).comp (W.selmerGroup τK m).subtype
  rw [f.finite_iff_finite_ker_range]
  refine ⟨Finite.of_injective (β := (W.torsionRes τ m).ker) (fun c ↦ ⟨c.1.1, c.2⟩)
    fun c d h ↦ by rw [Subtype.ext_iff, Subtype.ext_iff]; exact (congrArg Subtype.val h :),
    Finite.of_injective (β := (W⁄L).selmerGroup τL m) (fun c ↦ ⟨c.1, ?_⟩)
      fun c d h ↦ by rw [Subtype.ext_iff]; exact (congrArg Subtype.val h :)⟩
  obtain ⟨d, hd⟩ := c.2
  rw [← hd]
  exact W.torsionRes_mem_selmerGroup τ τK τL σ d.2

end Selmer

end WeierstrassCurve
