/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Basic
public import TauCeti.RepresentationTheory.Character.Twist
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Operations on raw Weil–Deligne parameters

For raw Weil–Deligne parameters `(V, r, N)` and `(V', r', N')`
(`TauCeti.WeilDeligneParameter`), this file constructs

* the **direct sum** `(V × V', r ⊕ r', N ⊕ N')` (`TauCeti.WeilDeligneParameter.sum`);
* the **tensor product** `(V ⊗ V', r ⊗ r', N ⊗ 1 + 1 ⊗ N')`
  (`TauCeti.WeilDeligneParameter.tensor`);
* the **dual** `(V^∨, r^∨, -Nᵗ)`, where `r^∨(w) = r(w⁻¹)ᵗ`
  (`TauCeti.WeilDeligneParameter.dual`);
* the **twist** `(V, χ r, N)` by a character `χ : W →* Eˣ` with open kernel
  (`TauCeti.WeilDeligneParameter.twist`).

The conjugation relation `r(w) N r(w)⁻¹ = q ^ deg w • N` holds for each because conjugation by
`r(w)` scales `N ⊗ 1` and `1 ⊗ N'` by the same factor, commutes with the transpose up to inverting
`w`, and is unchanged by a scalar. The kernel of the sum is the intersection of the two kernels;
for the other three the kernel only contains an open subgroup, so these need a topological group
`W`. Each operation is functorial on morphisms and isomorphisms of parameters (the dual
contravariantly), and the sum and the twist commute with transport. For finite-dimensional `V`
the double dual is isomorphic to the parameter through the canonical evaluation map
(`TauCeti.WeilDeligneParameter.dualDualIso`), so double duality recovers `N`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §4.1.
-/

public section

noncomputable section

namespace TauCeti

open Module TensorProduct

namespace WeilDeligneParameter

variable {E W V V' V₁ V₂ V₁' V₂' V₃ V₃' : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V₁] [Module E V₁] [AddCommGroup V₂] [Module E V₂]
  [AddCommGroup V₁'] [Module E V₁'] [AddCommGroup V₂'] [Module E V₂']
  [AddCommGroup V₃] [Module E V₃] [AddCommGroup V₃'] [Module E V₃']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- The conjugation relation evaluated at a vector: `r(w) (N (r(w⁻¹) v)) = q ^ deg w • N v`. -/
theorem r_apply_N_apply_r_inv_apply (D : WeilDeligneParameter E W V deg q) (w : W) (v : V) :
    D.r w (D.N (D.r w⁻¹ v)) = (q : E) ^ (deg w).toAdd • D.N v :=
  LinearMap.congr_fun (D.conj_N w) v

/-! ### Direct sums -/

/-- The product of two nilpotent endomorphisms is nilpotent. -/
private theorem isNilpotent_prodMap {f : Module.End E V} {g : Module.End E V'}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f.prodMap g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  have h (k : ℕ) : (f.prodMap g) ^ k = (f ^ k).prodMap (g ^ k) := by
    induction k with
    | zero => simp [LinearMap.prodMap_one]
    | succ k ih => rw [pow_succ, ih, LinearMap.prodMap_mul, ← pow_succ, ← pow_succ]
  refine ⟨max m n, ?_⟩
  rw [h, pow_eq_zero_of_le (le_max_left m n) hm, pow_eq_zero_of_le (le_max_right m n) hn,
    LinearMap.prodMap_zero]

/-- The **direct sum** `(V × V', r ⊕ r', N ⊕ N')` of two raw Weil–Deligne parameters. -/
def sum (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q) :
    WeilDeligneParameter E W (V × V') deg q where
  r := D.r.prod D'.r
  isOpen_ker := by
    have h : ((D.r.prod D'.r).ker : Set W) = (D.r.ker : Set W) ∩ D'.r.ker := by
      ext w
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_inter_iff]
      constructor
      · intro h
        refine ⟨LinearMap.ext fun v ↦ ?_, LinearMap.ext fun v' ↦ ?_⟩
        · simpa using congrArg Prod.fst (LinearMap.congr_fun h (v, 0))
        · simpa using congrArg Prod.snd (LinearMap.congr_fun h (0, v'))
      · rintro ⟨h, h'⟩
        ext x <;> simp [h, h']
    rw [h]
    exact D.isOpen_ker.inter D'.isOpen_ker
  N := D.N.prodMap D'.N
  isNilpotent_N := isNilpotent_prodMap D.isNilpotent_N D'.isNilpotent_N
  conj_N w := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · simpa using D.r_apply_N_apply_r_inv_apply w x.1
    · simpa using D'.r_apply_N_apply_r_inv_apply w x.2

variable (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)

@[simp]
theorem sum_r : (D.sum D').r = D.r.prod D'.r :=
  (rfl)

@[simp]
theorem sum_N : (D.sum D').N = D.N.prodMap D'.N :=
  (rfl)

variable {D₁ : WeilDeligneParameter E W V₁ deg q} {D₂ : WeilDeligneParameter E W V₂ deg q}
  {D₁' : WeilDeligneParameter E W V₁' deg q} {D₂' : WeilDeligneParameter E W V₂' deg q}
  {D₃ : WeilDeligneParameter E W V₃ deg q} {D₃' : WeilDeligneParameter E W V₃' deg q}

/-- The direct sum of two morphisms of parameters. -/
def Hom.sum (f : Hom D₁ D₂) (g : Hom D₁' D₂') : Hom (D₁.sum D₁') (D₂.sum D₂') where
  toLinearMap := f.toLinearMap.prodMap g.toLinearMap
  isIntertwining' w := LinearMap.ext fun x ↦ Prod.ext (f.map_r_apply w x.1) (g.map_r_apply w x.2)
  comp_N := LinearMap.ext fun x ↦ Prod.ext (f.map_N_apply x.1) (g.map_N_apply x.2)

@[simp]
theorem Hom.sum_apply (f : Hom D₁ D₂) (g : Hom D₁' D₂') (x : V₁ × V₁') :
    f.sum g x = (f x.1, g x.2) :=
  (rfl)

@[simp]
theorem Hom.sum_id : (Hom.id D₁).sum (Hom.id D₁') = Hom.id (D₁.sum D₁') :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

theorem Hom.sum_comp (f : Hom D₂ D₃) (g : Hom D₂' D₃') (f' : Hom D₁ D₂) (g' : Hom D₁' D₂') :
    (f.comp f').sum (g.comp g') = (f.sum g).comp (f'.sum g') :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

/-- The direct sum of two isomorphisms of parameters. -/
def Iso.sum (f : Iso D₁ D₂) (g : Iso D₁' D₂') : Iso (D₁.sum D₁') (D₂.sum D₂') :=
  Iso.ofBijective (f.toHom.sum g.toHom) (by
    rw [show ⇑(f.toHom.sum g.toHom) = Prod.map f g from funext fun x ↦ by simp; rfl]
    exact Prod.map_bijective.mpr ⟨f.bijective, g.bijective⟩)

@[simp]
theorem Iso.sum_apply (f : Iso D₁ D₂) (g : Iso D₁' D₂') (x : V₁ × V₁') :
    f.sum g x = (f x.1, g x.2) := by
  simp [Iso.sum]

/-- The direct sum commutes with transport. -/
theorem sum_transport (e : V ≃ₗ[E] V₁) (e' : V' ≃ₗ[E] V₁') :
    (D.transport e).sum (D'.transport e') = (D.sum D').transport (e.prodCongr e') := by
  ext w x <;> simp [transport_r_apply, transport_N_apply]

/-! ### Twists -/

variable [IsTopologicalGroup W]

/-- The **twist** `(V, χ r, N)` of a raw Weil–Deligne parameter by a character `χ : W →* Eˣ`
with open kernel. -/
def twist (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) : WeilDeligneParameter E W V deg q where
  r := Representation.charTwist χ D.r
  isOpen_ker := by
    refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ D.r.ker) (fun w hw ↦ ?_) (hχ.inter D.isOpen_ker)
    rw [MonoidHom.mem_ker, Representation.charTwist_apply, MonoidHom.mem_ker.mp hw.1,
      MonoidHom.mem_ker.mp hw.2, Units.val_one, one_smul]
  N := D.N
  isNilpotent_N := D.isNilpotent_N
  conj_N w := by
    ext v
    have h : ((χ w⁻¹ : E) * (χ w : E)) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply,
      Representation.charTwist_apply_apply, map_smul, LinearMap.smul_apply, smul_smul, h,
      one_smul]
    exact D.r_apply_N_apply_r_inv_apply w v

variable (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W))

@[simp]
theorem twist_r : (D.twist χ hχ).r = Representation.charTwist χ D.r :=
  (rfl)

@[simp]
theorem twist_N : (D.twist χ hχ).N = D.N :=
  (rfl)

/-- The twist of a morphism of parameters by a common character. -/
def Hom.twist (f : Hom D₁ D₂) : Hom (D₁.twist χ hχ) (D₂.twist χ hχ) where
  toLinearMap := f.toLinearMap
  isIntertwining' w := LinearMap.ext fun v ↦ by
    simp [f.map_r_apply]
  comp_N := f.comp_N

@[simp]
theorem Hom.twist_apply (f : Hom D₁ D₂) (v : V₁) : f.twist χ hχ v = f v :=
  (rfl)

@[simp]
theorem Hom.twist_id : (Hom.id D₁).twist χ hχ = Hom.id (D₁.twist χ hχ) :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

theorem Hom.twist_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) :
    (f.comp g).twist χ hχ = (f.twist χ hχ).comp (g.twist χ hχ) :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

/-- The twist of an isomorphism of parameters by a common character. -/
def Iso.twist (f : Iso D₁ D₂) : Iso (D₁.twist χ hχ) (D₂.twist χ hχ) :=
  Iso.ofBijective (f.toHom.twist χ hχ) (by
    rw [show ⇑(f.toHom.twist χ hχ) = f from funext fun v ↦ by simp]
    exact f.bijective)

@[simp]
theorem Iso.twist_apply (f : Iso D₁ D₂) (v : V₁) : f.twist χ hχ v = f v := by
  simp [Iso.twist]

/-- The twist commutes with transport. -/
theorem twist_transport (e : V ≃ₗ[E] V₁) :
    (D.transport e).twist χ hχ = (D.twist χ hχ).transport e := by
  ext w v <;> simp [transport_r_apply, transport_N_apply]

/-! ### Tensor products -/

/-- The **tensor product** `(V ⊗ V', r ⊗ r', N ⊗ 1 + 1 ⊗ N')` of two raw Weil–Deligne
parameters. -/
def tensor : WeilDeligneParameter E W (V ⊗[E] V') deg q where
  r := D.r.tprod D'.r
  isOpen_ker := by
    refine Subgroup.isOpen_mono (H₁ := D.r.ker ⊓ D'.r.ker) (fun w hw ↦ ?_)
      (D.isOpen_ker.inter D'.isOpen_ker)
    rw [MonoidHom.mem_ker, Representation.tprod_apply, MonoidHom.mem_ker.mp hw.1,
      MonoidHom.mem_ker.mp hw.2, TensorProduct.map_one]
  N := D.N.rTensor V' + D'.N.lTensor V
  isNilpotent_N := by
    refine Commute.isNilpotent_add ?_ ?_ ?_
    · ext v v'
      simp
    · obtain ⟨m, hm⟩ := D.isNilpotent_N
      exact ⟨m, by rw [LinearMap.rTensor_pow, hm, LinearMap.rTensor_zero]⟩
    · obtain ⟨m, hm⟩ := D'.isNilpotent_N
      exact ⟨m, by rw [LinearMap.lTensor_pow, hm, LinearMap.lTensor_zero]⟩
  conj_N w := by
    ext v v'
    simp [Representation.tprod_apply, r_apply_N_apply_r_inv_apply, Representation.self_inv_apply,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]

@[simp]
theorem tensor_r : (D.tensor D').r = D.r.tprod D'.r :=
  (rfl)

@[simp]
theorem tensor_N : (D.tensor D').N = D.N.rTensor V' + D'.N.lTensor V :=
  (rfl)

/-- The tensor product of two morphisms of parameters. -/
def Hom.tensor (f : Hom D₁ D₂) (g : Hom D₁' D₂') : Hom (D₁.tensor D₁') (D₂.tensor D₂') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' w := by
    ext v v'
    simp [Representation.tprod_apply, f.map_r_apply, g.map_r_apply]
  comp_N := by
    ext v v'
    simp [f.map_N_apply, g.map_N_apply]

@[simp]
theorem Hom.tensor_tmul (f : Hom D₁ D₂) (g : Hom D₁' D₂') (v : V₁) (v' : V₁') :
    f.tensor g (v ⊗ₜ v') = f v ⊗ₜ g v' :=
  (rfl)

@[simp]
theorem Hom.tensor_id : (Hom.id D₁).tensor (Hom.id D₁') = Hom.id (D₁.tensor D₁') :=
  Hom.ext (TensorProduct.ext' fun v v' ↦ by simp)

theorem Hom.tensor_comp (f : Hom D₂ D₃) (g : Hom D₂' D₃') (f' : Hom D₁ D₂) (g' : Hom D₁' D₂') :
    (f.comp f').tensor (g.comp g') = (f.tensor g).comp (f'.tensor g') :=
  Hom.ext (TensorProduct.ext' fun v v' ↦ by simp)

/-- The tensor product of two isomorphisms of parameters. -/
def Iso.tensor (f : Iso D₁ D₂) (g : Iso D₁' D₂') : Iso (D₁.tensor D₁') (D₂.tensor D₂') :=
  Iso.ofBijective (f.toHom.tensor g.toHom) (by
    rw [show ⇑(f.toHom.tensor g.toHom) = TensorProduct.congr f.toLinearEquiv g.toLinearEquiv from
      congrArg DFunLike.coe (TensorProduct.ext' fun v v' ↦ by simp)]
    exact (TensorProduct.congr f.toLinearEquiv g.toLinearEquiv).bijective)

@[simp]
theorem Iso.tensor_tmul (f : Iso D₁ D₂) (g : Iso D₁' D₂') (v : V₁) (v' : V₁') :
    f.tensor g (v ⊗ₜ v') = f v ⊗ₜ g v' := by
  simp [Iso.tensor]

/-! ### Duals -/

/-- The transpose of a nilpotent endomorphism is nilpotent. -/
private theorem isNilpotent_dualMap {f : Module.End E V} (hf : IsNilpotent f) :
    IsNilpotent f.dualMap := by
  obtain ⟨m, hm⟩ := hf
  have h (k : ℕ) : f.dualMap ^ k = (f ^ k).dualMap := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, ih, pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearMap.dualMap_comp_dualMap]
  refine ⟨m, ?_⟩
  rw [h, hm]
  ext
  simp

/-- The **dual** `(V^∨, r^∨, -Nᵗ)` of a raw Weil–Deligne parameter, with
`r^∨(w) = r(w⁻¹)ᵗ`. -/
def dual : WeilDeligneParameter E W (Module.Dual E V) deg q where
  r := D.r.dual
  isOpen_ker := by
    refine Subgroup.isOpen_mono (fun w hw ↦ ?_) D.isOpen_ker
    rw [MonoidHom.mem_ker, Representation.dual_apply, MonoidHom.mem_ker.mp (inv_mem hw)]
    ext
    rfl
  N := -D.N.dualMap
  isNilpotent_N := IsNilpotent.neg (R := Module.End E (Module.Dual E V))
    (isNilpotent_dualMap D.isNilpotent_N)
  conj_N w := by
    ext φ v
    simp [Representation.dual_apply, Module.Dual.transpose_apply,
      r_apply_N_apply_r_inv_apply]

@[simp]
theorem dual_r : D.dual.r = D.r.dual :=
  (rfl)

/-- Duality changes the monodromy `N` to `-Nᵗ`. -/
@[simp]
theorem dual_N : D.dual.N = -D.N.dualMap :=
  (rfl)

/-- The transpose of a morphism of parameters, a morphism between the duals in the opposite
direction. -/
def Hom.dual (f : Hom D₁ D₂) : Hom D₂.dual D₁.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' w := by
    ext φ v
    simp [Representation.dual_apply, Module.Dual.transpose_apply, f.map_r_apply]
  comp_N := by
    ext φ v
    simp [f.map_N_apply]

@[simp]
theorem Hom.dual_apply (f : Hom D₁ D₂) (φ : Module.Dual E V₂) : f.dual φ = φ ∘ₗ f.toLinearMap :=
  (rfl)

@[simp]
theorem Hom.dual_id : (Hom.id D₁).dual = Hom.id D₁.dual :=
  Hom.ext (LinearMap.ext fun φ ↦ by simp)

theorem Hom.dual_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) : (f.comp g).dual = g.dual.comp f.dual :=
  Hom.ext (LinearMap.ext fun φ ↦ by simp [LinearMap.comp_assoc])

/-- The transpose of an isomorphism of parameters. -/
def Iso.dual (f : Iso D₁ D₂) : Iso D₂.dual D₁.dual :=
  Iso.ofBijective f.toHom.dual (by
    rw [show ⇑f.toHom.dual = f.toLinearEquiv.dualMap from funext fun φ ↦ by ext; simp]
    exact f.toLinearEquiv.dualMap.bijective)

@[simp]
theorem Iso.dual_apply (f : Iso D₁ D₂) (φ : Module.Dual E V₂) :
    f.dual φ = φ ∘ₗ f.toLinearEquiv.toLinearMap := by
  simp [Iso.dual]

/-- **Double duality.** For finite-dimensional `V`, the canonical evaluation map is an
isomorphism from a parameter to its double dual; in particular the monodromy of the double dual
is `N`. -/
def dualDualIso [FiniteDimensional E V] : Iso D D.dual.dual where
  toLinearEquiv := Module.evalEquiv E V
  isIntertwining' w := by
    ext v φ
    simp [Representation.dual_apply, Module.Dual.transpose_apply]
  comp_N := by
    ext v φ
    simp

@[simp]
theorem dualDualIso_apply [FiniteDimensional E V] (v : V) :
    D.dualDualIso v = Module.Dual.eval E V v :=
  (rfl)

end WeilDeligneParameter

end TauCeti
