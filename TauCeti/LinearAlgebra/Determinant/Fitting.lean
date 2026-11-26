/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Endomorphism
public import TauCeti.LinearAlgebra.End.Fitting
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The determinant line of an endomorphism on an invariant summand

Let `T` be an endomorphism of a module `V = p ⊕ q` over a ring, where both summands are
`T`-invariant and `T` is bijective on `q`. Then the kernel of `T` lies in `p`, and the inclusion
of `p` identifies the kernel and the cokernel of the restriction `T₀ = T|p` with those of `T`
(`LinearMap.kerRestrictEquiv`, `LinearMap.cokerRestrictEquiv`). Over a commutative ring this
gives an isomorphism `e : det T₀ ≃ det T` of determinant lines (`LinearMap.detLineRestrictEquiv`),
with no choice beyond the splitting. For a finite-dimensional vector space, against the canonical
trivializations `LinearMap.detLineEndEquiv` of the two lines, `e` is multiplication by the inverse
determinant of `T₁ = T|q`, up to a sign:

`detLineEndEquiv T (e x) = (-1) ^ (dim (ker T) * dim q) * (det T₁)⁻¹ * detLineEndEquiv T₀ x`

(`LinearMap.detLineEndEquiv_detLineRestrictEquiv`). The sign disappears for the normalized
generators `LinearMap.detLineEndGenerator`, which are the ones that vary continuously in families:
`e` sends the normalized generator of `det T₀` to `(det T₁)⁻¹` times that of `det T`
(`LinearMap.detLineRestrictEquiv_detLineEndGenerator`). So over an ordered field the two
normalized orientations correspond exactly when `det T₁ > 0`
(`LinearMap.sameRay_detLineRestrictEquiv_detLineEndGenerator_iff`). For `p = 0` these are
`LinearMap.detLineEndEquiv_eq_inv_det_mul` and `LinearMap.detLineEndGenerator_eq_det_smul`.

The canonical instance is the Fitting decomposition `V = V₀ ⊕ V₁` into the generalized kernel
`V₀ = ⨆ n, ker (T ^ n)`, on which `T` is nilpotent, and the stable range `V₁ = ⨅ n, range (T ^ n)`,
on which `T` is invertible (`TauCeti.LinearAlgebra.End.Fitting`). It involves no choice of
complement, so the determinant line of `T` is that of its restriction to the whole generalized
kernel `V₀`, with the factor `det (T|V₁)`
(`LinearMap.detLineRestrictEquiv_iSup_ker_pow_detLineEndGenerator`). For `T = 1 - P`
the summand `V₀` is the generalized eigenspace of `P` for the eigenvalue `1`. This is how the
orientation of a degenerate return map `P` reduces to that eigenspace: when `det (1 - P) = 0` its
sign is not available, while `det (1 - P)` restricted to the complementary invariant summand is
nonzero and the full determinant line of the generalized eigenspace is kept.

## Main definitions

* `LinearMap.kerRestrictEquiv`, `LinearMap.cokerRestrictEquiv`: the kernel and cokernel of `T` are
  those of its restriction to `p`.
* `LinearMap.detLineRestrictEquiv`: the induced isomorphism `det (T|p) ≃ det T`.

## Main results

* `LinearMap.detLineEndEquiv_detLineRestrictEquiv`: the canonical trivializations differ by
  `(-1) ^ (dim (ker T) * dim q) * (det (T|q))⁻¹`.
* `LinearMap.detLineRestrictEquiv_detLineEndGenerator`: the normalized generators differ by
  `(det (T|q))⁻¹`.
* `LinearMap.sameRay_detLineRestrictEquiv_detLineEndGenerator_iff`: over an ordered field, the
  normalized orientations agree exactly when `det (T|q) > 0`.
* `LinearMap.detLineRestrictEquiv_iSup_ker_pow_detLineEndGenerator`: the case of the Fitting
  decomposition.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant lines).
* H. Fitting, *Die Theorie der Automorphismenringe Abelscher Gruppen und ihr Analogon bei nicht
  kommutativen Gruppen*, Math. Ann. **107** (1933), 514–542.
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

section Restrict

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {T : M →ₗ[R] M}
  {p q : Submodule R M} (hpq : IsCompl p q) (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T x ∈ q)

include hpq hp hq in
/-- If `x ∈ p` is `T a + T b` with `a ∈ p` and `b ∈ q`, then `x = T a`, since `T b` lies in
`p ⊓ q = ⊥`. -/
private theorem eq_of_add_mem_range {a b : M} (ha : a ∈ p) (hb : b ∈ q) {x : M} (hx : x ∈ p)
    (h : x = T a + T b) : x = T a := by
  have hTb : T b ∈ p ⊓ q := ⟨by simpa [h] using sub_mem hx (hp a ha), hq b hb⟩
  rw [hpq.inf_eq_bot, Submodule.mem_bot] at hTb
  rw [h, hTb, add_zero]

include hpq hp hq in
/-- The kernel of `T` lies in `p` when `T` is injective on `q`. -/
private theorem ker_le (hT : Function.Injective (T.restrict hq)) : ker T ≤ p := by
  intro v hv
  obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hpq.codisjoint v
  have hab : T a + T b = 0 := by simpa using hv
  have hTa : 0 = T a := eq_of_add_mem_range hpq hp hq ha hb (zero_mem p) hab.symm
  have hTb : T b = 0 := by rwa [← hTa, zero_add] at hab
  have hb0 : (⟨b, hb⟩ : q) = 0 := hT (Subtype.ext (by simpa using hTb))
  simpa [show b = 0 from congrArg Subtype.val hb0] using ha

/-- The summand `q` lies in the range of `T` when `T` is surjective on `q`. -/
private theorem le_range (hT : Function.Surjective (T.restrict hq)) : q ≤ range T := fun b hb ↦ by
  obtain ⟨c, hc⟩ := hT ⟨b, hb⟩
  exact ⟨c, congrArg Subtype.val hc⟩

section Ker

variable (hT : Function.Injective (T.restrict hq))

/-- **The kernel of `T` is that of its restriction to `p`**, when `M = p ⊕ q` with both summands
`T`-invariant and `T` injective on `q`; the isomorphism is induced by the inclusion of `p`. -/
def kerRestrictEquiv : ker (T.restrict hp) ≃ₗ[R] ker T :=
  LinearEquiv.ofBijective
    ((p.subtype.comp (ker (T.restrict hp)).subtype).codRestrict (ker T) fun x ↦
      mem_ker.2 (congrArg Subtype.val (mem_ker.1 x.property)))
    ⟨fun x y h ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)), fun v ↦
      ⟨⟨⟨v, ker_le hpq hp hq hT v.property⟩, mem_ker.2 (Subtype.ext (mem_ker.1 v.property))⟩,
        rfl⟩⟩

/-- `LinearMap.kerRestrictEquiv` is the inclusion of `p`. -/
@[simp]
theorem coe_kerRestrictEquiv_apply (x : ker (T.restrict hp)) :
    (kerRestrictEquiv hpq hp hq hT x : M) = ((x : p) : M) :=
  (rfl)

/-- The inverse of `LinearMap.kerRestrictEquiv` sends a vector of the kernel of `T` to itself, as a
vector of `p`. -/
@[simp]
theorem coe_kerRestrictEquiv_symm_apply (v : ker T) :
    (((kerRestrictEquiv hpq hp hq hT).symm v : p) : M) = v := by
  rw [← coe_kerRestrictEquiv_apply hpq hp hq hT, LinearEquiv.apply_symm_apply]

end Ker

section Coker

variable (hT : Function.Surjective (T.restrict hq))

/-- **The cokernel of `T` is that of its restriction to `p`**, when `M = p ⊕ q` with both summands
`T`-invariant and `T` surjective on `q`; the isomorphism is induced by the inclusion of `p`. -/
def cokerRestrictEquiv : (p ⧸ range (T.restrict hp)) ≃ₗ[R] (M ⧸ range T) :=
  LinearEquiv.ofBijective
    ((range (T.restrict hp)).mapQ (range T) p.subtype fun x ⟨y, hy⟩ ↦
      ⟨y, by simpa using congrArg Subtype.val hy⟩)
    ⟨by
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      obtain ⟨v, hv⟩ := hx
      obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hpq.codisjoint v
      refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
      exact (eq_of_add_mem_range hpq hp hq ha hb x.property (by simpa using hv.symm)).symm, by
      intro y
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
      obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hpq.codisjoint v
      refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
      rw [Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      simpa using neg_mem (le_range hq hT hb)⟩

/-- `LinearMap.cokerRestrictEquiv` sends the class of `x ∈ p` to the class of `x`. -/
@[simp]
theorem cokerRestrictEquiv_mk (x : p) :
    cokerRestrictEquiv hpq hp hq hT (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : M) :=
  (rfl)

/-- The inverse of `LinearMap.cokerRestrictEquiv` sends the class of `x ∈ p` modulo the range of
`T` to its class modulo the range of the restriction. -/
@[simp]
theorem cokerRestrictEquiv_symm_mk (x : p) :
    (cokerRestrictEquiv hpq hp hq hT).symm (Submodule.Quotient.mk (x : M)) =
      Submodule.Quotient.mk x := by
  rw [LinearEquiv.symm_apply_eq, cokerRestrictEquiv_mk]

end Coker

end Restrict

section DetLineRestrict

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {T : M →ₗ[R] M}
  {p q : Submodule R M} (hpq : IsCompl p q) (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T x ∈ q)
  (hT : Function.Bijective (T.restrict hq))

/-- **The determinant line of `T` is that of its restriction to `p`**, when `M = p ⊕ q` with both
summands `T`-invariant and `T` bijective on `q`: the isomorphism induced by the identifications
`LinearMap.kerRestrictEquiv` of the kernels and `LinearMap.cokerRestrictEquiv` of the cokernels. -/
def detLineRestrictEquiv : (T.restrict hp).detLine ≃ₗ[R] T.detLine :=
  detLineCongrKerCoker (kerRestrictEquiv hpq hp hq hT.1) (cokerRestrictEquiv hpq hp hq hT.2)

/-- `LinearMap.detLineRestrictEquiv` is the isomorphism `LinearMap.detLineCongrKerCoker` induced by
`LinearMap.kerRestrictEquiv` and `LinearMap.cokerRestrictEquiv`. -/
theorem detLineRestrictEquiv_def :
    detLineRestrictEquiv hpq hp hq hT =
      detLineCongrKerCoker (kerRestrictEquiv hpq hp hq hT.1) (cokerRestrictEquiv hpq hp hq hT.2) :=
  (rfl)

/-- `LinearMap.detLineRestrictEquiv` on a pure tensor: the kernel factor is carried along
`LinearMap.kerRestrictEquiv`, the dual cokernel factor along the inverse of
`LinearMap.cokerRestrictEquiv`. -/
@[simp]
theorem detLineRestrictEquiv_tmul (x : TauCeti.detLine R (ker (T.restrict hp)))
    (φ : Dual R (TauCeti.detLine R (p ⧸ range (T.restrict hp)))) :
    detLineRestrictEquiv hpq hp hq hT (x ⊗ₜ φ) =
      LinearEquiv.detLineCongr (kerRestrictEquiv hpq hp hq hT.1) x ⊗ₜ
        (φ ∘ₗ (LinearEquiv.detLineCongr (cokerRestrictEquiv hpq hp hq hT.2)).symm.toLinearMap) :=
  detLineCongrKerCoker_tmul _ _ x φ

end DetLineRestrict

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {T : V →ₗ[K] V}
  {p q : Submodule K V}

section CokerDetLine

variable (hpq : IsCompl p q) (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T x ∈ q)

/-- The inverse of the isomorphism of cokernel determinant lines induced by
`LinearMap.cokerRestrictEquiv` sends the exterior product of the classes of vectors of `p` to the
exterior product of their classes modulo the range of the restriction. -/
private theorem detLineCongr_cokerRestrictEquiv_symm_ιMulti
    (hT : Function.Surjective (T.restrict hq))
    (z₀ : Fin (finrank K (p ⧸ range (T.restrict hp))) → p)
    (hc : finrank K (V ⧸ range T) = finrank K (p ⧸ range (T.restrict hp))) :
    (LinearEquiv.detLineCongr (cokerRestrictEquiv hpq hp hq hT)).symm
        (exteriorPower.ιMulti K _ ((range T).mkQ ∘ p.subtype ∘ z₀ ∘ Fin.cast hc)) =
      exteriorPower.ιMulti K _ ((range (T.restrict hp)).mkQ ∘ z₀) := by
  rw [LinearEquiv.detLineCongr_symm, LinearEquiv.detLineCongr_ιMulti]
  congr 1
  funext i
  simp

/-- The determinant of `T` on a summand where it is injective is nonzero. -/
private theorem det_restrict_ne_zero [FiniteDimensional K V]
    (hT : Function.Injective (T.restrict hq)) : LinearMap.det (T.restrict hq) ≠ 0 := fun h ↦
  LinearMap.det_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 hT)

end CokerDetLine

/-! ### The canonical trivialization on an invariant summand -/

section DetLine

/-- The exterior product of a family `a` of vectors of `p`, followed by a family `v₀` of vectors
of `p` and a family `w` of vectors of `q`, is the product of the exterior products of `a ++ v₀`
and of `w`. -/
private theorem ιMulti_append_append_subtype {k k' r₀ r n : ℕ} (a : Fin k → p) (v₀ : Fin r₀ → p)
    (w : Fin n → q) (hk : k' = k) (hr : r = r₀ + n) :
    ExteriorAlgebra.ιMulti K (k' + r) (Fin.append (p.subtype ∘ a ∘ Fin.cast hk)
        (Fin.append (p.subtype ∘ v₀) (q.subtype ∘ w) ∘ Fin.cast hr)) =
      ExteriorAlgebra.map p.subtype (ExteriorAlgebra.ιMulti K _ (Fin.append a v₀)) *
        ExteriorAlgebra.map q.subtype (ExteriorAlgebra.ιMulti K _ w) := by
  rw [← Function.comp_assoc, TauCeti.ExteriorAlgebra.ιMulti_append_comp_cast,
    ← ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.map_apply_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_append, mul_assoc]

/-- The exterior product of the images under `T` of a family `v₀` of vectors of `p` and a family
`w` of `dim q` vectors of `q`, followed by a family `z₀` of vectors of `p`, is `det (T|q)` times the
product of the exterior products of `T|p ∘ v₀ ++ z₀` and of `w`, up to the sign of moving `z₀`
past `w`. -/
private theorem ιMulti_append_comp_append_subtype (hp : ∀ x ∈ p, T x ∈ p)
    (hq : ∀ x ∈ q, T x ∈ q) {r₀ c r c' : ℕ} (v₀ : Fin r₀ → p)
    (w : Fin (finrank K q) → q) (z₀ : Fin c → p) (hr : r = r₀ + finrank K q) (hc : c' = c) :
    ExteriorAlgebra.ιMulti K (r + c') (Fin.append
        (T ∘ Fin.append (p.subtype ∘ v₀) (q.subtype ∘ w) ∘ Fin.cast hr)
        (p.subtype ∘ z₀ ∘ Fin.cast hc)) =
      (LinearMap.det (T.restrict hq) * (-1) ^ (c * finrank K q)) •
        (ExteriorAlgebra.map p.subtype
            (ExteriorAlgebra.ιMulti K _ (Fin.append (T.restrict hp ∘ v₀) z₀)) *
          ExteriorAlgebra.map q.subtype (ExteriorAlgebra.ιMulti K _ w)) := by
  have hT : T ∘ Fin.append (p.subtype ∘ v₀) (q.subtype ∘ w) =
      Fin.append (p.subtype ∘ (T.restrict hp ∘ v₀)) (q.subtype ∘ (T.restrict hq ∘ w)) :=
    Fin.comp_append _ _ _
  have hw : ExteriorAlgebra.ιMulti K _ (q.subtype ∘ (T.restrict hq ∘ w)) =
      LinearMap.det (T.restrict hq) • ExteriorAlgebra.ιMulti K _ (q.subtype ∘ w) := by
    rw [← ExteriorAlgebra.map_apply_ιMulti, LinearMap.ιMulti_comp_eq_det_smul, map_smul,
      ExteriorAlgebra.map_apply_ιMulti]
  -- Split both sides into exterior products of the families in `p` and in `q`.
  rw [← Function.comp_assoc, ← Function.comp_assoc,
    TauCeti.ExteriorAlgebra.ιMulti_append_comp_cast, hT, ← ExteriorAlgebra.ιMulti_mul_ιMulti, hw,
    ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
    TauCeti.ExteriorAlgebra.ιMulti_comp_append]
  -- Collect the scalars, then move the family `w` in `q` past `z₀`.
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [TauCeti.ExteriorAlgebra.ιMulti_mul_ιMulti_eq_neg_one_pow_smul (q.subtype ∘ w), mul_smul_comm,
    smul_smul]

variable [FiniteDimensional K V] (hpq : IsCompl p q) (hp : ∀ x ∈ p, T x ∈ p)
  (hq : ∀ x ∈ q, T x ∈ q) (hT : Function.Bijective (T.restrict hq))

include hpq hT in
/-- The range of `T` has dimension `dim (range T|p) + dim q`. -/
private theorem finrank_range_eq_add :
    finrank K (range T) = finrank K (range (T.restrict hp)) + finrank K q := by
  have := T.finrank_range_add_finrank_ker
  have := (T.restrict hp).finrank_range_add_finrank_ker
  have := Submodule.finrank_add_eq_of_isCompl hpq
  have := (kerRestrictEquiv hpq hp hq hT.1).finrank_eq
  omega

/-- The comparison behind `LinearMap.detLineEndEquiv_detLineRestrictEquiv`, at the element
`α₀ ⊗ ξ₀` of the determinant line of `T₀ = T|p` given by exterior products `β₀ = D₀ • γ₀` as in
`LinearMap.detLineEndEquiv_tmul`. Extending these by a basis of `q` gives exterior products for
`T`, which are `D₀` and `det (T|q)` times the same nonzero element, up to a sign. -/
private theorem detLineEndEquiv_detLineRestrictEquiv_mul
    (v₀ : Fin (finrank K (range (T.restrict hp))) → p)
    (z₀ : Fin (finrank K (p ⧸ range (T.restrict hp))) → p) {β₀ γ₀ : TauCeti.detLine K p}
    {ξ₀ : Dual K (TauCeti.detLine K (p ⧸ range (T.restrict hp)))}
    (hβ₀ : (β₀ : ExteriorAlgebra K p) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((ker (T.restrict hp)).subtype ∘ Module.finBasis K (ker (T.restrict hp))) v₀))
    (hγ₀ : (γ₀ : ExteriorAlgebra K p) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (T.restrict hp ∘ v₀) z₀))
    (hξ₀ : ξ₀ (exteriorPower.ιMulti K _ ((range (T.restrict hp)).mkQ ∘ z₀)) = 1)
    (hγ₀ne : γ₀ ≠ 0) :
    T.detLineEndEquiv (detLineRestrictEquiv hpq hp hq hT
        (exteriorPower.ιMulti K _ (Module.finBasis K (ker (T.restrict hp))) ⊗ₜ ξ₀)) *
        (LinearMap.det (T.restrict hq) *
          (-1) ^ (finrank K (p ⧸ range (T.restrict hp)) * finrank K q)) =
      (T.restrict hp).detLineEndEquiv
        (exteriorPower.ιMulti K _ (Module.finBasis K (ker (T.restrict hp))) ⊗ₜ ξ₀) := by
  set u₀ := ⇑(Module.finBasis K (ker (T.restrict hp)))
  have hβγ₀ := eq_detLineEndEquiv_smul (T.restrict hp) u₀ v₀ z₀ hβ₀ hγ₀ hξ₀
  have hk : finrank K (ker (T.restrict hp)) = finrank K (ker T) :=
    (kerRestrictEquiv hpq hp hq hT.1).finrank_eq
  have hc : finrank K (V ⧸ range T) = finrank K (p ⧸ range (T.restrict hp)) :=
    (cokerRestrictEquiv hpq hp hq hT.2).finrank_eq.symm
  set w := ⇑(Module.finBasis K q)
  set u := kerRestrictEquiv hpq hp hq hT.1 ∘ u₀ ∘ Fin.cast hk.symm
  set v := Fin.append (p.subtype ∘ v₀) (q.subtype ∘ w) ∘
    Fin.cast (finrank_range_eq_add hpq hp hq hT)
  set z := p.subtype ∘ z₀ ∘ Fin.cast hc
  set ξ := ξ₀ ∘ₗ (LinearEquiv.detLineCongr (cokerRestrictEquiv hpq hp hq hT.2)).symm.toLinearMap
  have hξ : ξ (exteriorPower.ιMulti K _ ((range T).mkQ ∘ z)) = 1 := by
    simp only [ξ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [detLineCongr_cokerRestrictEquiv_symm_ιMulti, hξ₀]
  have hV := T.finrank_range_add_finrank_ker
  have hV' := (range T).finrank_quotient_add_finrank
  obtain ⟨β, hβ⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K)
    (a := Fin.append ((ker T).subtype ∘ u) v) (by omega)
  obtain ⟨γ, hγ⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K)
    (a := Fin.append (T ∘ v) z) (by omega)
  -- Both are multiples of the product `X` of `γ₀` and the basis of `q`, which is nonzero.
  set X := ExteriorAlgebra.map p.subtype (γ₀ : ExteriorAlgebra K p) *
    ExteriorAlgebra.map q.subtype (ExteriorAlgebra.ιMulti K _ w)
  have hβX : (β : ExteriorAlgebra K V) =
      (T.restrict hp).detLineEndEquiv (exteriorPower.ιMulti K _ u₀ ⊗ₜ ξ₀) • X := by
    have hu : (ker T).subtype ∘ u =
        p.subtype ∘ ((ker (T.restrict hp)).subtype ∘ u₀) ∘ Fin.cast hk.symm := by
      funext i
      simp [u]
    rw [hβ, hu, ιMulti_append_append_subtype, ← hβ₀, hβγ₀, Submodule.coe_smul, map_smul,
      smul_mul_assoc]
  have hX : X ≠ 0 := by
    have hind : LinearIndependent K (Fin.append ((T.restrict hp) ∘ v₀) z₀) := by
      rw [← exteriorPower.ιMulti_ne_zero_iff]
      intro h
      exact hγ₀ne (by
        rw [← ZeroMemClass.coe_eq_zero, hγ₀, ← exteriorPower.ιMulti_apply_coe, h,
          ZeroMemClass.coe_zero])
    simp only [X, hγ₀, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]
    rw [← exteriorPower.ιMulti_apply_coe, ne_eq, ZeroMemClass.coe_eq_zero]
    exact exteriorPower.ιMulti_append_subtype_ne_zero hpq.disjoint hind
      (Module.finBasis K q).linearIndependent
  have hβγ := congrArg Subtype.val (eq_detLineEndEquiv_smul T u v z hβ hγ hξ)
  rw [Submodule.coe_smul, hβX, hγ, ιMulti_append_comp_append_subtype hp hq, ← hγ₀, smul_smul]
    at hβγ
  rw [detLineRestrictEquiv_tmul, LinearEquiv.detLineCongr_ιMulti]
  exact (smul_left_injective K hX hβγ).symm

/-- The formula of `LinearMap.detLineEndEquiv_detLineRestrictEquiv` at one nonzero element of the
determinant line of the restriction. -/
private theorem exists_ne_zero_detLineEndEquiv_detLineRestrictEquiv :
    ∃ y : (T.restrict hp).detLine, y ≠ 0 ∧
      T.detLineEndEquiv (detLineRestrictEquiv hpq hp hq hT y) =
        (-1) ^ (finrank K (ker T) * finrank K q) * (LinearMap.det (T.restrict hq))⁻¹ *
          (T.restrict hp).detLineEndEquiv y := by
  set T₀ := T.restrict hp
  obtain ⟨v₀, z₀, β₀, γ₀, ξ₀, hβ₀, hγ₀, hξ₀, hspan⟩ := TauCeti.exists_spanning_ιMulti_append
    (ker T₀).injective_subtype T₀.exact_subtype_ker_map T₀.exact_map_mkQ_range
    (range T₀).mkQ_surjective
  set u₀ := ⇑(Module.finBasis K (ker T₀))
  have hβγ₀ := eq_detLineEndEquiv_smul T₀ u₀ v₀ z₀ hβ₀ hγ₀ hξ₀
  have hβ₀ne : β₀ ≠ 0 := fun h ↦ by
    have : Subsingleton (TauCeti.detLine K p) :=
      ⟨fun x y ↦ by obtain ⟨r, rfl⟩ := hspan x; obtain ⟨s, rfl⟩ := hspan y; simp [h]⟩
    simpa using (TauCeti.finrank_detLine (R := K) (V := p)).symm.trans finrank_zero_of_subsingleton
  have hDκ := detLineEndEquiv_detLineRestrictEquiv_mul hpq hp hq hT v₀ z₀ hβ₀ hγ₀ hξ₀
    fun h ↦ hβ₀ne (by rw [hβγ₀, h, smul_zero])
  refine ⟨exteriorPower.ιMulti K _ u₀ ⊗ₜ ξ₀, fun h ↦ hβ₀ne ?_, ?_⟩
  · rw [hβγ₀, h, map_zero, zero_smul]
  have hdet := det_restrict_ne_zero hq hT.1
  have hck : finrank K (p ⧸ range T₀) = finrank K (ker T) := by
    have := T₀.finrank_range_add_finrank_ker
    have := (range T₀).finrank_quotient_add_finrank
    have : finrank K (ker T₀) = finrank K (ker T) := (kerRestrictEquiv hpq hp hq hT.1).finrank_eq
    omega
  rw [← hDκ]
  generalize T.detLineEndEquiv _ = D
  rw [hck]
  have hs : ((-1 : K) ^ (finrank K (ker T) * finrank K q)) ^ 2 = 1 := by
    rw [sq, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  generalize LinearMap.det (T.restrict hq) = d at hdet ⊢
  generalize (-1 : K) ^ (finrank K (ker T) * finrank K q) = s at hs ⊢
  rw [show s * d⁻¹ * (D * (d * s)) = D * s ^ 2 * (d * d⁻¹) by ring, hs, mul_inv_cancel₀ hdet]
  ring

/-- **The canonical trivialization of `det T` through an invariant summand.** Let `V = p ⊕ q`
with both summands `T`-invariant and `T` bijective on `q`. Under the identification
`e = LinearMap.detLineRestrictEquiv` of the determinant line of the restriction `T₀` of `T` to `p`
with that of `T`, the canonical trivialization of `det T` is that of `det T₀` divided by the
determinant of the restriction `T₁` of `T` to `q`, up to the sign
`(-1) ^ (dim (ker T) * dim q)`:

`detLineEndEquiv T (e x) = (-1) ^ (dim (ker T) * dim q) * (det T₁)⁻¹ * detLineEndEquiv T₀ x`.

For `p = 0` this is `LinearMap.detLineEndEquiv_eq_inv_det_mul`. The sign disappears for the
normalized generators (`LinearMap.detLineRestrictEquiv_detLineEndGenerator`). -/
theorem detLineEndEquiv_detLineRestrictEquiv (x : (T.restrict hp).detLine) :
    T.detLineEndEquiv (detLineRestrictEquiv hpq hp hq hT x) =
      (-1) ^ (finrank K (ker T) * finrank K q) * (LinearMap.det (T.restrict hq))⁻¹ *
        (T.restrict hp).detLineEndEquiv x := by
  obtain ⟨y, hy, h⟩ := exists_ne_zero_detLineEndEquiv_detLineRestrictEquiv hpq hp hq hT
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' _ hy).mp (T.restrict hp).finrank_detLine x
  rw [map_smul, map_smul, h, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The normalized generators through an invariant summand.** Let `V = p ⊕ q` with both summands
`T`-invariant and `T` bijective on `q`. The identification `LinearMap.detLineRestrictEquiv` of the
determinant line of the restriction `T₀` of `T` to `p` with that of `T` sends the normalized
generator of `det T₀` to `(det T₁)⁻¹` times the normalized generator of `det T`, where `T₁` is the
restriction of `T` to `q`. For `p = 0` this is `LinearMap.detLineEndGenerator_eq_det_smul`. -/
theorem detLineRestrictEquiv_detLineEndGenerator :
    detLineRestrictEquiv hpq hp hq hT (T.restrict hp).detLineEndGenerator =
      (LinearMap.det (T.restrict hq))⁻¹ • T.detLineEndGenerator := by
  refine T.detLineEndEquiv.injective ?_
  rw [detLineEndEquiv_detLineRestrictEquiv, detLineEndEquiv_detLineEndGenerator, map_smul,
    detLineEndEquiv_detLineEndGenerator, (kerRestrictEquiv hpq hp hq hT.1).finrank_eq,
    ← Submodule.finrank_add_eq_of_isCompl hpq, smul_eq_mul,
    show finrank K (ker T) * (finrank K p + finrank K q + 1) =
      finrank K (ker T) * finrank K q + finrank K (ker T) * (finrank K p + 1) by ring, pow_add]
  ring

/-- **Orientations through an invariant summand.** Over an ordered field, in the situation of
`LinearMap.detLineRestrictEquiv_detLineEndGenerator`, the normalized generator of `det T₀`,
carried to `det T`, lies on the ray of the normalized generator of `det T` exactly when the
determinant of `T₁` is positive. -/
theorem sameRay_detLineRestrictEquiv_detLineEndGenerator_iff [LinearOrder K]
    [IsStrictOrderedRing K] :
    SameRay K (detLineRestrictEquiv hpq hp hq hT (T.restrict hp).detLineEndGenerator)
        T.detLineEndGenerator ↔ 0 < LinearMap.det (T.restrict hq) := by
  rw [detLineRestrictEquiv_detLineEndGenerator]
  exact (sameRay_smul_left_iff_of_ne (M := T.detLine) T.detLineEndGenerator_ne_zero
    (inv_ne_zero (det_restrict_ne_zero hq hT.1))).trans inv_pos

end DetLine

/-! ### The Fitting decomposition -/

section Fitting

variable [FiniteDimensional K V] (T)

/-- **The determinant line of an endomorphism through its Fitting decomposition.** In finite
dimension, write `V = V₀ ⊕ V₁` with `V₀ = ⨆ n, ker (T ^ n)` the generalized kernel of `T`, on which
`T` is nilpotent, and `V₁ = ⨅ n, range (T ^ n)` its stable range, on which `T` is invertible. The
identification `LinearMap.detLineRestrictEquiv` of the determinant line of the nilpotent part
`T₀ = T|V₀` with that of `T` sends the normalized generator of `det T₀` to `(det (T|V₁))⁻¹` times
the normalized generator of `det T`. This decomposition involves no choice. -/
theorem detLineRestrictEquiv_iSup_ker_pow_detLineEndGenerator
    (hp : ∀ x ∈ ⨆ n, ker (T ^ n), T x ∈ ⨆ n, ker (T ^ n) := T.mapsTo_iSup_ker_pow)
    (hq : ∀ x ∈ ⨅ n, range (T ^ n), T x ∈ ⨅ n, range (T ^ n) := T.mapsTo_iInf_range_pow) :
    detLineRestrictEquiv (isCompl_iSup_ker_pow_iInf_range_pow T) hp hq
        (bijective_restrict_iInf_range_pow T hq) (T.restrict hp).detLineEndGenerator =
      (LinearMap.det (T.restrict hq))⁻¹ • T.detLineEndGenerator :=
  detLineRestrictEquiv_detLineEndGenerator _ _ _ _

end Fitting

end LinearMap
